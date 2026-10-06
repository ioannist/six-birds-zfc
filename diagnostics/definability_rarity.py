#!/usr/bin/env python3
"""Definability-rarity diagnostics for WP-8 exhibit 2."""

from __future__ import annotations

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


RESULT_PATH = ROOT / "diagnostics" / "results" / "definability_rarity_last_run.json"
TABLE_PATH = ROOT / "diagnostics" / "tables" / "definability_rarity_table.tex"
FIGURE_PATH = ROOT / "diagnostics" / "figures" / "definability_rarity.png"
GENERATOR = "diagnostics/definability_rarity.py"
SEED = 20260611
SAMPLES = 200_000
ZCRIT = 4.0
MIN_EXPECTED_FOR_Z = 10.0


CONFIGS: list[dict[str, Any]] = [
    {"name": "identity_8_8", "partition": [1, 1, 1, 1, 1, 1, 1, 1]},
    {"name": "balanced_8_4", "partition": [2, 2, 2, 2]},
    {"name": "balanced_10_5", "partition": [2, 2, 2, 2, 2]},
    {"name": "balanced_12_4", "partition": [3, 3, 3, 3]},
    {"name": "uneven_12_4", "partition": [1, 2, 4, 5]},
    {"name": "singleton_mixed_12_6", "partition": [1, 1, 2, 2, 3, 3]},
    {"name": "balanced_16_4", "partition": [4, 4, 4, 4]},
    {"name": "singleton_mixed_18_9", "partition": [1, 1, 1, 1, 2, 2, 3, 3, 4]},
    {"name": "tiny_balanced_24_4", "partition": [6, 6, 6, 6]},
]


def fail_config(config_name: str, payload: dict[str, Any]) -> None:
    report = {"config": config_name, "counterexample": payload}
    print(report, file=sys.stderr)
    raise SystemExit(1)


def block_slices(partition: list[int]) -> list[slice]:
    out: list[slice] = []
    start = 0
    for size in partition:
        out.append(slice(start, start + size))
        start += size
    return out


def analyze_config(rng: np.random.Generator, config: dict[str, Any]) -> dict[str, Any]:
    name = config["name"]
    partition = list(config["partition"])
    if any(size <= 0 for size in partition):
        fail_config(name, {"reason": "empty block", "partition": partition})
    n = int(sum(partition))
    k = int(len(partition))
    bits = rng.integers(0, 2, size=(SAMPLES, n), dtype=np.uint8)

    definable = np.ones(SAMPLES, dtype=bool)
    strict = np.zeros(SAMPLES, dtype=bool)
    nontrivial_splits: list[np.ndarray] = []

    for block in block_slices(partition):
        values = bits[:, block]
        constant = np.all(values == values[:, [0]], axis=1)
        split = ~constant
        definable &= constant
        strict |= split
        if values.shape[1] >= 2:
            nontrivial_splits.append(split)

    if nontrivial_splits:
        split_every_nontrivial = np.logical_and.reduce(nontrivial_splits)
    else:
        split_every_nontrivial = np.ones(SAMPLES, dtype=bool)

    definable_count = int(definable.sum())
    strict_count = int(strict.sum())
    split_every_count = int(split_every_nontrivial.sum())

    predicted = 2.0 ** (-(n - k))
    empirical = definable_count / SAMPLES
    strict_predicted = 1.0 - predicted
    empirical_strict = strict_count / SAMPLES
    abs_error = abs(empirical - predicted)
    rel_error = abs_error / predicted if predicted else 0.0
    expected_count = SAMPLES * predicted
    expected_complement = SAMPLES * (1.0 - predicted)

    if predicted in (0.0, 1.0):
        standard_error = 0.0
        z_score = 0.0 if empirical == predicted else math.inf
        gate_mode = "exact"
        gate_passed = empirical == predicted
    elif expected_count < MIN_EXPECTED_FOR_Z or expected_complement < MIN_EXPECTED_FOR_Z:
        standard_error = math.sqrt(predicted * (1.0 - predicted) / SAMPLES)
        z_score = ((empirical - predicted) / standard_error) if standard_error else 0.0
        gate_mode = "observational_low_expected"
        gate_passed = True
    else:
        standard_error = math.sqrt(predicted * (1.0 - predicted) / SAMPLES)
        z_score = (empirical - predicted) / standard_error
        gate_mode = "z"
        gate_passed = abs(z_score) <= ZCRIT

    if not gate_passed:
        fail_config(name, {
            "empirical": empirical,
            "predicted": predicted,
            "z_score": z_score,
            "zcrit": ZCRIT,
            "gate_mode": gate_mode,
        })

    nontriv_sizes = [size for size in partition if size >= 2]
    if nontriv_sizes:
        exact_split_every = float(np.prod([1.0 - 2.0 ** (1 - size) for size in nontriv_sizes]))
        union_bound_sum = float(sum(2.0 ** (1 - size) for size in nontriv_sizes))
        union_bound_lower = max(0.0, 1.0 - union_bound_sum)
        min_nontrivial_block = int(min(nontriv_sizes))
    else:
        exact_split_every = 1.0
        union_bound_sum = 0.0
        union_bound_lower = 1.0
        min_nontrivial_block = None

    split_every_fraction = split_every_count / SAMPLES
    split_se = math.sqrt(exact_split_every * (1.0 - exact_split_every) / SAMPLES)
    if split_se == 0:
        split_z = 0.0 if split_every_fraction == exact_split_every else math.inf
        split_gate_mode = "exact"
        split_gate_passed = split_every_fraction == exact_split_every
    elif min(exact_split_every, 1.0 - exact_split_every) * SAMPLES < MIN_EXPECTED_FOR_Z:
        split_z = (split_every_fraction - exact_split_every) / split_se
        split_gate_mode = "observational_low_expected"
        split_gate_passed = True
    else:
        split_z = (split_every_fraction - exact_split_every) / split_se
        split_gate_mode = "z"
        split_gate_passed = abs(split_z) <= ZCRIT
    if not split_gate_passed:
        fail_config(name, {"reason": "block-splitting frequency failed statistical gate",
                           "empirical": split_every_fraction, "predicted": exact_split_every,
                           "z_score": split_z})

    return {
        "name": name,
        "partition": partition,
        "N": n,
        "K": k,
        "N_minus_K": n - k,
        "M": SAMPLES,
        "definable_count": definable_count,
        "empirical_definable_fraction": empirical,
        "predicted_definable_fraction": predicted,
        "abs_error": abs_error,
        "relative_error": rel_error,
        "standard_error": standard_error,
        "z_score": z_score,
        "zcrit": ZCRIT,
        "expected_definable_count": expected_count,
        "gate_mode": gate_mode,
        "gate_passed": gate_passed,
        "strict_count": strict_count,
        "empirical_strict_fraction": empirical_strict,
        "predicted_strict_fraction": strict_predicted,
        "split_every_nontrivial_count": split_every_count,
        "empirical_split_every_nontrivial_fraction": split_every_fraction,
        "exact_split_every_nontrivial_fraction": exact_split_every,
        "split_gate_mode": split_gate_mode,
        "split_gate_passed": split_gate_passed,
        "split_z_score": split_z,
        "union_bound_constant_block_sum": union_bound_sum,
        "union_bound_split_lower": union_bound_lower,
        "min_nontrivial_block_size": min_nontrivial_block,
    }


def fmt_float(x: float) -> str:
    if math.isinf(x):
        return "inf"
    if x == 0:
        return "0"
    if abs(x) < 0.001 or abs(x) >= 1000:
        return f"{x:.3e}"
    return f"{x:.6f}"


def make_tables(result: dict[str, Any]) -> None:
    rows = []
    for cfg in result["configs"]:
        rows.append([
            cfg["name"],
            cfg["N"],
            cfg["K"],
            cfg["N_minus_K"],
            cfg["M"],
            fmt_float(cfg["predicted_definable_fraction"]),
            fmt_float(cfg["empirical_definable_fraction"]),
            fmt_float(cfg["z_score"]),
            cfg["gate_mode"],
        ])
    tex_table(
        TABLE_PATH,
        "Definability rarity: empirical fractions versus the exact finite-forcing prediction.",
        "tab:definability-rarity",
        ["Config", "N", "K", "N-K", "M", "Pred.", "Emp.", "z", "Gate"],
        rows,
    )

    companion_rows = []
    for cfg in result["configs"]:
        companion_rows.append([
            cfg["name"],
            cfg["partition"],
            cfg["min_nontrivial_block_size"],
            fmt_float(cfg["empirical_split_every_nontrivial_fraction"]),
            fmt_float(cfg["exact_split_every_nontrivial_fraction"]),
            fmt_float(cfg["union_bound_split_lower"]),
        ])
    tex_table(
        TABLE_PATH,
        "Nothing-Stays-Constant companion: splitting every non-singleton block.",
        "tab:definability-rarity-splitting",
        ["Config", "Blocks", "Min block", "Emp. split", "Exact split", "UB lower"],
        companion_rows,
        append=True,
    )


def make_figure(result: dict[str, Any]) -> None:
    configs = result["configs"]
    xs = [cfg["N_minus_K"] for cfg in configs]
    predicted = [cfg["predicted_definable_fraction"] for cfg in configs]
    floor = 0.5 / SAMPLES
    empirical = [max(cfg["empirical_definable_fraction"], floor) for cfg in configs]

    FIGURE_PATH.parent.mkdir(parents=True, exist_ok=True)
    plt.figure(figsize=(7, 4.5))
    plt.scatter(xs, predicted, label="predicted", marker="o")
    plt.scatter(xs, empirical, label="empirical", marker="x")
    plt.yscale("log")
    plt.xlabel("N-K")
    plt.ylabel("definable fraction")
    plt.title("Definability rarity")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend()
    plt.tight_layout()
    plt.savefig(FIGURE_PATH, dpi=160)
    plt.close()


def main() -> None:
    rng = np.random.default_rng(SEED)
    configs = [analyze_config(rng, cfg) for cfg in CONFIGS]

    by_block_count: dict[int, list[dict[str, Any]]] = {}
    for cfg in configs:
        if len(set(cfg["partition"])) == 1 and cfg["min_nontrivial_block_size"] is not None:
            by_block_count.setdefault(cfg["K"], []).append(cfg)
    for group in by_block_count.values():
        balanced_sorted = sorted(group, key=lambda cfg: cfg["min_nontrivial_block_size"])
        for left, right in zip(balanced_sorted, balanced_sorted[1:]):
            if right["empirical_split_every_nontrivial_fraction"] + 0.02 < left["empirical_split_every_nontrivial_fraction"]:
                fail_config(right["name"], {
                    "reason": "monotone split sanity failed within fixed K",
                    "previous": left["name"],
                    "previous_fraction": left["empirical_split_every_nontrivial_fraction"],
                    "current_fraction": right["empirical_split_every_nontrivial_fraction"],
                })

    result = {
        "seed": SEED,
        "samples_per_config": SAMPLES,
        "zcrit": ZCRIT,
        "min_expected_for_z_gate": MIN_EXPECTED_FOR_Z,
        "all_passed": all(cfg["gate_passed"] and cfg["split_gate_passed"] for cfg in configs),
        "configs": configs,
    }
    dump_result(RESULT_PATH, result, GENERATOR)
    make_tables(result)
    make_figure(result)
    print(f"wrote {RESULT_PATH}")
    print(f"wrote {TABLE_PATH}")
    print(f"wrote {FIGURE_PATH}")


if __name__ == "__main__":
    main()
