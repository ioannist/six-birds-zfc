#!/usr/bin/env python3
"""Finite Cohen bridge diagnostics for WP-8 exhibit 3."""

from __future__ import annotations

import itertools
import math
import os
import sys
from pathlib import Path
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
os.environ.setdefault("MPLCONFIGDIR", str(ROOT / "diagnostics" / ".mplconfig"))

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from lib_artifact import dump_result, tex_table


RESULT_PATH = ROOT / "diagnostics" / "results" / "finite_cohen_last_run.json"
TABLE_PATH = ROOT / "diagnostics" / "tables" / "finite_cohen_table.tex"
FIGURE_PATH = ROOT / "diagnostics" / "figures" / "finite_cohen.png"
GENERATOR = "diagnostics/finite_cohen.py"
SEED = 20260611
MAX_EXHAUSTIVE_N = 5
SCALING_SAMPLES = 100_000

UNDEF = -1
Condition = tuple[int, ...]
Predicate = tuple[int, ...]
Lens = tuple[int, ...]


def fail_check(check: str, payload: dict[str, Any]) -> None:
    print({"check": check, "counterexample": payload}, file=sys.stderr)
    raise SystemExit(1)


def conditions(n: int) -> list[Condition]:
    return list(itertools.product([UNDEF, 0, 1], repeat=n))


def predicates(n: int) -> list[Predicate]:
    return list(itertools.product([0, 1], repeat=n))


def surjective_lenses(n: int, k: int) -> list[Lens]:
    out: list[Lens] = []
    for f in itertools.product(range(k), repeat=n):
        if set(f) == set(range(k)):
            out.append(tuple(f))
    return out


def blocks(f: Lens, k: int) -> list[tuple[int, ...]]:
    return [tuple(i for i, value in enumerate(f) if value == x) for x in range(k)]


def definable_predicates(f: Lens, k: int) -> list[Predicate]:
    out: list[Predicate] = []
    for block_bits in itertools.product([0, 1], repeat=k):
        out.append(tuple(block_bits[f[i]] for i in range(len(f))))
    return out


def extends(q: Condition, p: Condition) -> bool:
    return all(p_i == UNDEF or q_i == p_i for p_i, q_i in zip(p, q))


def subset_of_predicate(p: Condition, h: Predicate) -> bool:
    return all(value == UNDEF or value == h[i] for i, value in enumerate(p))


def total_condition(h: Predicate) -> Condition:
    return tuple(h)


def in_D(p: Condition, g: Predicate) -> bool:
    return any(value != UNDEF and value != g[i] for i, value in enumerate(p))


def in_E(p: Condition, block: tuple[int, ...]) -> bool:
    assigned = [p[i] for i in block if p[i] != UNDEF]
    return 0 in assigned and 1 in assigned


def h_splits_block(h: Predicate, block: tuple[int, ...]) -> bool:
    values = {h[i] for i in block}
    return len(values) >= 2


def condition_constant_total_on_block(p: Condition, block: tuple[int, ...]) -> bool:
    values = [p[i] for i in block]
    return all(value != UNDEF for value in values) and len(set(values)) <= 1


def extension_map(conds: list[Condition]) -> dict[Condition, list[Condition]]:
    return {p: [q for q in conds if extends(q, p)] for p in conds}


def representative(obj: Any) -> Any:
    if isinstance(obj, tuple):
        return list(obj)
    return obj


def run_exhaustive() -> dict[str, Any]:
    summary = {
        "max_N": MAX_EXHAUSTIVE_N,
        "lens_count": 0,
        "A1_meeting_D_instances": 0,
        "A2_meeting_E_instances": 0,
        "A3_density_D_instances": 0,
        "A4_density_E_instances": 0,
        "A3_condition_tests": 0,
        "A4_condition_tests": 0,
        "exact_counting_lenses": 0,
        "all_passed": True,
        "by_NK": [],
    }

    for n in range(0, MAX_EXHAUSTIVE_N + 1):
        conds = conditions(n)
        exts = extension_map(conds)
        hs = predicates(n)
        for k in ([0] if n == 0 else range(1, n + 1)):
            lenses = surjective_lenses(n, k)
            nk_record = {"N": n, "K": k, "lenses": len(lenses)}
            for f in lenses:
                summary["lens_count"] += 1
                blks = blocks(f, k)
                gs = definable_predicates(f, k)
                constant_hs = [h for h in hs if all(not h_splits_block(h, b) for b in blks)]
                split_all_count = sum(all(h_splits_block(h, b) for b in blks if len(b) >= 2)
                                      for h in hs)
                expected_split_count = math.prod((2 ** len(b) - 2) if len(b) >= 2 else 2
                                                for b in blks)
                if (len(gs) != 2 ** k or set(gs) != set(constant_hs)
                        or split_all_count != expected_split_count):
                    fail_check("exact_counting", {"f": f, "K": k,
                                                "split_count": split_all_count})
                summary["exact_counting_lenses"] += 1

                for h in hs:
                    for g in gs:
                        meet = any(subset_of_predicate(p, h) and in_D(p, g) for p in conds)
                        expected = h != g
                        summary["A1_meeting_D_instances"] += 1
                        if meet != expected:
                            fail_check("A1_meeting_D", {
                                "N": n,
                                "K": k,
                                "f": representative(f),
                                "h": representative(h),
                                "g": representative(g),
                                "meet": meet,
                                "expected": expected,
                            })

                for h in hs:
                    for block_id, block in enumerate(blks):
                        if len(block) < 2:
                            continue
                        meet = any(subset_of_predicate(p, h) and in_E(p, block) for p in conds)
                        expected = h_splits_block(h, block)
                        summary["A2_meeting_E_instances"] += 1
                        if meet != expected:
                            fail_check("A2_meeting_E", {
                                "N": n,
                                "K": k,
                                "f": representative(f),
                                "block_id": block_id,
                                "block": representative(block),
                                "h": representative(h),
                                "meet": meet,
                                "expected": expected,
                            })

                for g in gs:
                    failure = {
                        p for p in conds
                        if not any(in_D(q, g) for q in exts[p])
                    }
                    expected_failure = {total_condition(g)}
                    summary["A3_density_D_instances"] += 1
                    summary["A3_condition_tests"] += len(conds)
                    if failure != expected_failure:
                        fail_check("A3_density_D", {
                            "N": n,
                            "K": k,
                            "f": representative(f),
                            "g": representative(g),
                            "failure": [representative(x) for x in sorted(failure)],
                            "expected": [representative(x) for x in sorted(expected_failure)],
                        })

                for block_id, block in enumerate(blks):
                    if len(block) < 2:
                        continue
                    failure = {
                        p for p in conds
                        if not any(in_E(q, block) for q in exts[p])
                    }
                    expected_failure = {
                        p for p in conds if condition_constant_total_on_block(p, block)
                    }
                    summary["A4_density_E_instances"] += 1
                    summary["A4_condition_tests"] += len(conds)
                    if failure != expected_failure:
                        fail_check("A4_density_E", {
                            "N": n,
                            "K": k,
                            "f": representative(f),
                            "block_id": block_id,
                            "block": representative(block),
                            "failure": [representative(x) for x in sorted(failure)],
                            "expected": [representative(x) for x in sorted(expected_failure)],
                        })
            summary["by_NK"].append(nk_record)

    return summary


def balanced_partition(n: int, k: int) -> list[int]:
    base = n // k
    extra = n % k
    return [base + (1 if i < extra else 0) for i in range(k)]


def scaling_trial(rng: np.random.Generator, n: int, k: int) -> dict[str, Any]:
    partition = balanced_partition(n, k)
    bits = rng.integers(0, 2, size=(SCALING_SAMPLES, n), dtype=np.uint8)
    definable = np.ones(SCALING_SAMPLES, dtype=bool)
    start = 0
    for size in partition:
        block = bits[:, start:start + size]
        definable &= np.all(block == block[:, [0]], axis=1)
        start += size
    meets_all_D = ~definable
    empirical = float(meets_all_D.mean())
    predicted = 1.0 - 2.0 ** (-(n - k))
    se = math.sqrt(predicted * (1.0 - predicted) / SCALING_SAMPLES)
    if predicted == 1.0 or predicted == 0.0:
        gate_mode = "exact"
        gate_passed = empirical == predicted
        z_score = 0.0 if gate_passed else math.inf
    elif min(predicted, 1.0 - predicted) * SCALING_SAMPLES < 10:
        gate_mode = "observational_low_expected"
        gate_passed = True
        z_score = (empirical - predicted) / se
    else:
        gate_mode = "z"
        z_score = (empirical - predicted) / se
        gate_passed = abs(z_score) <= 4.0
    if not gate_passed:
        fail_check("B_scaling", {"N": n, "K": k, "z_score": z_score,
                                 "predicted": predicted, "empirical": empirical})
    return {
        "N": n,
        "K": k,
        "N_minus_K": n - k,
        "partition": partition,
        "samples": SCALING_SAMPLES,
        "empirical_meets_all_D_fraction": empirical,
        "predicted_meets_all_D_fraction": predicted,
        "abs_error": abs(empirical - predicted),
        "gate_mode": gate_mode,
        "gate_passed": gate_passed,
        "z_score": z_score,
    }


def run_scaling() -> dict[str, Any]:
    rng = np.random.default_rng(SEED)
    k = 4
    rows = [scaling_trial(rng, n, k) for n in [4, 6, 8, 10, 12, 14, 16, 18, 20, 24]]
    for left, right in zip(rows, rows[1:]):
        if right["predicted_meets_all_D_fraction"] < left["predicted_meets_all_D_fraction"]:
            fail_check("B_scaling", {"reason": "predicted fraction decreased"})
    return {
        "seed": SEED,
        "samples_per_N": SCALING_SAMPLES,
        "fixed_K": k,
        "rows": rows,
    }


def fmt_float(x: float) -> str:
    if x == 0:
        return "0"
    if abs(x) < 0.001 or abs(x) >= 1000:
        return f"{x:.3e}"
    return f"{x:.6f}"


def make_tables(result: dict[str, Any]) -> None:
    part_a = result["part_A"]
    a_rows = [
        ["lenses", part_a["lens_count"], "surjective lenses checked"],
        ["A1", part_a["A1_meeting_D_instances"], "meeting D iff h != g"],
        ["A2", part_a["A2_meeting_E_instances"], "meeting E iff h splits block"],
        ["A3", part_a["A3_density_D_instances"], "F(D_g) = total g"],
        ["A4", part_a["A4_density_E_instances"], "F(E_x) = total constant block"],
    ]
    tex_table(
        TABLE_PATH,
        "Finite Cohen exhaustive structural cross-checks.",
        "tab:finite-cohen-exhaustive",
        ["Item", "Instances", "Assertion"],
        a_rows,
    )

    b_rows = []
    for row in result["part_B"]["rows"]:
        b_rows.append([
            row["N"],
            row["K"],
            row["N_minus_K"],
            row["samples"],
            fmt_float(row["predicted_meets_all_D_fraction"]),
            fmt_float(row["empirical_meets_all_D_fraction"]),
            fmt_float(row["abs_error"]),
        ])
    tex_table(
        TABLE_PATH,
        "Finite disagreement-meeting scaling for meeting every D_g requirement.",
        "tab:finite-cohen-scaling",
        ["N", "K", "N-K", "M", "Pred.", "Emp.", "Abs. err."],
        b_rows,
        append=True,
    )


def make_figure(result: dict[str, Any]) -> None:
    rows = result["part_B"]["rows"]
    xs = [row["N"] for row in rows]
    pred = [row["predicted_meets_all_D_fraction"] for row in rows]
    emp = [row["empirical_meets_all_D_fraction"] for row in rows]
    FIGURE_PATH.parent.mkdir(parents=True, exist_ok=True)
    plt.figure(figsize=(7, 4.5))
    plt.plot(xs, pred, marker="o", label="predicted")
    plt.plot(xs, emp, marker="x", label="empirical")
    plt.ylim(0.0, 1.02)
    plt.xlabel("N with K=4")
    plt.ylabel("P(meets every D_g)")
    plt.title("Finite Cohen disagreement-meeting probability")
    plt.grid(True, alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIGURE_PATH, dpi=160)
    plt.close()


def main() -> None:
    part_a = run_exhaustive()
    part_b = run_scaling()
    result = {
        "part_A": part_a,
        "part_B": part_b,
        "all_passed": part_a["all_passed"],
    }
    dump_result(RESULT_PATH, result, GENERATOR)
    make_tables(result)
    make_figure(result)
    print(f"wrote {RESULT_PATH}")
    print(f"wrote {TABLE_PATH}")
    print(f"wrote {FIGURE_PATH}")


if __name__ == "__main__":
    main()
