#!/usr/bin/env python3
"""HF-slice falsification diagnostics for WP-8 exhibit 1."""

from __future__ import annotations

import random
import itertools
import sys
from functools import lru_cache
from pathlib import Path
from typing import Callable, Iterable

from lib_artifact import dump_result, tex_table


ROOT = Path(__file__).resolve().parents[1]
RESULT_PATH = ROOT / "diagnostics" / "results" / "hf_slice_last_run.json"
TABLE_PATH = ROOT / "diagnostics" / "tables" / "hf_slice_table.tex"
GENERATOR = "diagnostics/hf_slice.py"
SEED = 20260611
MAX_RANK = 4
PAIR_SAMPLES = 200
UNION_SAMPLES = 200
SEPARATION_SAMPLES = 200
COLLECTION_SAMPLES = 200

HFSet = frozenset
EMPTY = frozenset()


def powerset(items: tuple[HFSet, ...]) -> list[HFSet]:
    out: list[HFSet] = []
    n = len(items)
    for mask in range(1 << n):
        out.append(frozenset(items[i] for i in range(n) if (mask >> i) & 1))
    return out


def build_slices(max_rank: int) -> list[set[HFSet]]:
    """Return cumulative slices of all HF sets with rank <= n."""
    slices: list[set[HFSet]] = [set([EMPTY])]
    current = set([EMPTY])
    for _ in range(max_rank):
        elems = tuple(sorted(current, key=encode))
        current = set(powerset(elems))
        slices.append(current)
    return slices


@lru_cache(maxsize=None)
def rank(a: HFSet) -> int:
    if not a:
        return 0
    return 1 + max(rank(x) for x in a)


@lru_cache(maxsize=None)
def encode(a: HFSet) -> str:
    if not a:
        return "{}"
    return "{" + ",".join(sorted(encode(x) for x in a)) + "}"


def succ(a: HFSet) -> HFSet:
    return frozenset(set(a) | {a})


def union_set(a: HFSet) -> HFSet:
    out = set()
    for x in a:
        out.update(x)
    return frozenset(out)


def sample_from(rng: random.Random, xs: tuple[HFSet, ...]) -> HFSet:
    return xs[rng.randrange(len(xs))]


def fail_check(name: str, counterexample: dict) -> None:
    payload = {"check": name, "counterexample": counterexample}
    print(payload, file=sys.stderr)
    raise SystemExit(1)


def record(passed: bool, samples: int, witness: dict | str | int) -> dict:
    return {"passed": passed, "samples": samples, "witness": witness}


def check_c1_extensionality(all_sets: tuple[HFSet, ...]) -> dict:
    # Cross-check the tree/set representation against independent bit coding.
    # Testing uniqueness in a Python set alone would pass by construction.
    @lru_cache(maxsize=None)
    def code(a: HFSet) -> int:
        return sum(1 << code(x) for x in a)

    @lru_cache(maxsize=None)
    def decode(n: int) -> HFSet:
        return frozenset(decode(i) for i in range(n.bit_length()) if (n >> i) & 1)

    seen: dict[int, HFSet] = {}
    for a in all_sets:
        c = code(a)
        if decode(c) != a or (c in seen and seen[c] != a):
            fail_check("C1", {"set": encode(a), "code": c})
        seen[c] = a
    if set(seen) != set(range(len(all_sets))):
        fail_check("C1", {"reason": "Ackermann codes do not cover the initial segment"})
    return record(True, len(all_sets), {"duplicates": 0, "Ackermann_round_trips": len(seen)})


def check_c8_power_set(source: tuple[HFSet, ...], universe: set[HFSet]) -> dict:
    for a in source:
        p = frozenset(powerset(tuple(a)))
        if p not in universe or len(p) != 2 ** len(a) or any(not s.issubset(a) for s in p):
            fail_check("C8", {"set": encode(a), "power_set": encode(p)})
    return record(True, len(source), {"exhaustive_source": "rank <= 3"})


def check_c9_transport(source: tuple[HFSet, ...], targets: tuple[HFSet, ...],
                       universe: set[HFSet]) -> dict:
    count = 0
    for a in source:
        for values in itertools.product(targets, repeat=len(a)):
            count += 1
            image = frozenset(values)
            if image not in universe or len(image) > len(a):
                fail_check("C9", {"domain": encode(a), "image": encode(image)})
    return record(True, count, {"exhaustive_domains": "rank <= 3", "target_count": len(targets)})


def check_c2_pairing(rng: random.Random, source: tuple[HFSet, ...], universe: set[HFSet]) -> dict:
    for i in range(PAIR_SAMPLES):
        a = sample_from(rng, source)
        b = sample_from(rng, source)
        pair = frozenset([a, b])
        expected_rank = max(rank(a), rank(b)) + 1
        if pair not in universe or rank(pair) != expected_rank:
            fail_check("C2", {
                "sample": i,
                "a": encode(a),
                "b": encode(b),
                "pair": encode(pair),
                "rank_pair": rank(pair),
                "expected_rank": expected_rank,
                "in_universe": pair in universe,
            })
    return record(True, PAIR_SAMPLES, {"sampled_pairs": PAIR_SAMPLES})


def check_c3_union(rng: random.Random, universe_tuple: tuple[HFSet, ...], universe: set[HFSet]) -> dict:
    for i in range(UNION_SAMPLES):
        a = sample_from(rng, universe_tuple)
        u = union_set(a)
        if u not in universe or rank(u) > rank(a):
            fail_check("C3", {
                "sample": i,
                "a": encode(a),
                "union": encode(u),
                "rank_a": rank(a),
                "rank_union": rank(u),
                "in_universe": u in universe,
            })
    return record(True, UNION_SAMPLES, {"sampled_unions": UNION_SAMPLES})


def gate_factory(index: int) -> Callable[[HFSet], bool]:
    return lambda x: ((rank(x) + len(encode(x)) + index) % 2) == 0


def check_c4_separation(rng: random.Random, universe_tuple: tuple[HFSet, ...], universe: set[HFSet]) -> dict:
    for i in range(SEPARATION_SAMPLES):
        a = sample_from(rng, universe_tuple)
        gate = gate_factory(i)
        subset = frozenset(x for x in a if gate(x))
        if subset not in universe or not subset.issubset(a):
            fail_check("C4", {
                "sample": i,
                "a": encode(a),
                "subset": encode(subset),
                "in_universe": subset in universe,
                "is_subset": subset.issubset(a),
            })
    return record(True, SEPARATION_SAMPLES, {"sampled_gates": SEPARATION_SAMPLES})


def check_c5_finite_collection(rng: random.Random, source: tuple[HFSet, ...], universe: set[HFSet]) -> dict:
    for i in range(COLLECTION_SAMPLES):
        length = rng.randrange(0, 6)
        items = [sample_from(rng, source) for _ in range(length)]
        collection = frozenset(items)
        unique_items = set(items)
        ok_members = all((x in collection) == (x in unique_items) for x in source)
        if collection not in universe or not ok_members:
            fail_check("C5", {
                "sample": i,
                "items": [encode(x) for x in items],
                "collection": encode(collection),
                "in_universe": collection in universe,
                "membership_ok": ok_members,
            })
    return record(True, COLLECTION_SAMPLES, {"sampled_lists": COLLECTION_SAMPLES})


def check_c6_foundation(universe_tuple: tuple[HFSet, ...]) -> dict:
    edge_count = 0
    for a in universe_tuple:
        if a in a:
            fail_check("C6", {"self_member": encode(a)})
        for m in a:
            edge_count += 1
            if not rank(m) < rank(a):
                fail_check("C6", {
                    "a": encode(a),
                    "member": encode(m),
                    "rank_a": rank(a),
                    "rank_member": rank(m),
                })
    return record(True, edge_count, {"membership_edges": edge_count, "self_members": 0})


def is_inductive(a: HFSet) -> bool:
    return EMPTY in a and all(succ(x) in a for x in a)


def check_c7_not_inductive(universe_tuple: tuple[HFSet, ...]) -> dict:
    for a in universe_tuple:
        if is_inductive(a):
            fail_check("C7", {"inductive_candidate": encode(a), "size": len(a)})
    return record(True, len(universe_tuple), {"inductive_candidates": 0})


def make_tables(result: dict) -> None:
    sizes = result["rank_sizes"]
    size_rows = [[row["rank_bound"], row["cumulative_size"]] for row in sizes]
    tex_table(
        TABLE_PATH,
        "HF cumulative slice sizes generated by diagnostics/hf_slice.py.",
        "tab:hf-slice-sizes",
        ["Rank bound", "Cumulative size"],
        size_rows,
    )
    check_rows = [
        [name, "pass" if data["passed"] else "fail", data["samples"], data["residual"]]
        for name, data in result["checks"].items()
    ]
    tex_table(
        TABLE_PATH,
        "HF-slice falsification checks generated from the last run JSON.",
        "tab:hf-slice-checks",
        ["Check", "Status", "Samples", "Residual"],
        check_rows,
        append=True,
    )


def main() -> None:
    rng = random.Random(SEED)
    slices = build_slices(MAX_RANK)
    rank_sizes = [
        {"rank_bound": n, "cumulative_stage": n + 1, "cumulative_size": len(slices[n])}
        for n in range(len(slices))
    ]
    universe = slices[MAX_RANK]
    universe_tuple = tuple(sorted(universe, key=encode))
    source = tuple(sorted(slices[MAX_RANK - 1], key=encode))

    raw_checks = {
        "C1_extensionality": check_c1_extensionality(universe_tuple),
        "C2_pairing": check_c2_pairing(rng, source, universe),
        "C3_union": check_c3_union(rng, universe_tuple, universe),
        "C4_separation": check_c4_separation(rng, universe_tuple, universe),
        "C5_finite_collection": check_c5_finite_collection(rng, source, universe),
        "C6_foundation_rank_audit": check_c6_foundation(universe_tuple),
        "C7_no_inductive_set": check_c7_not_inductive(universe_tuple),
        "C8_power_set": check_c8_power_set(source, universe),
        "C9_transport": check_c9_transport(source, tuple(slices[2]), universe),
    }
    checks = {
        name: {
            "passed": data["passed"],
            "samples": data["samples"],
            "residual": 0,
            "witness": data["witness"],
        }
        for name, data in raw_checks.items()
    }
    result = {
        "seed": SEED,
        "rank_bound": MAX_RANK,
        "rank_sizes": rank_sizes,
        "checks": checks,
    }
    dump_result(RESULT_PATH, result, GENERATOR)
    make_tables(result)
    print(f"wrote {RESULT_PATH}")
    print(f"wrote {TABLE_PATH}")


if __name__ == "__main__":
    main()
