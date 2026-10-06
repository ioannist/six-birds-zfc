"""Extract plot data for the paper's diagnostics figure from the stored diagnostic runs.

Reads diagnostics/results/*.json (never re-samples) and writes whitespace-separated
tables that pgfplots reads in paper/figures/fig_diagnostics.tex.
Run from the repository root:  python3 paper/figures/data/make_fig_data.py
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent

rarity = json.loads((ROOT / "diagnostics/results/definability_rarity_last_run.json").read_text())
with (OUT / "rarity.dat").open("w") as fh:
    fh.write("nk pred emp mode split_exact split_emp\n")
    for c in rarity["configs"]:
        emp = c["empirical_definable_fraction"]
        fh.write(f'{c["N_minus_K"]} {c["predicted_definable_fraction"]:.10g} '
                 f'{emp if emp > 0 else "nan"} {c["gate_mode"]} '
                 f'{c["exact_split_every_nontrivial_fraction"]:.10g} '
                 f'{c["empirical_split_every_nontrivial_fraction"]:.10g}\n')

cohen = json.loads((ROOT / "diagnostics/results/finite_cohen_last_run.json").read_text())
with (OUT / "scaling.dat").open("w") as fh:
    fh.write("N K nk pred emp\n")
    for r in cohen["part_B"]["rows"]:
        fh.write(f'{r["N"]} {r["K"]} {r["N"] - r["K"]} {r["predicted_meets_all_D_fraction"]:.10g} '
                 f'{r["empirical_meets_all_D_fraction"]:.10g}\n')
