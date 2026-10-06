# Diagnostics Artifact Contract

Diagnostics exhibits are generated artifacts, not hand-maintained tables.

Each exhibit script must:

1. run a deterministic seeded computation;
2. write `diagnostics/results/<name>_last_run.json`;
3. generate `diagnostics/tables/<name>_table.tex` from that JSON;
4. exit nonzero with a counterexample record if a falsification check fails.

The paper should `\input{}` generated tables from `diagnostics/tables/`. Numbers are not
hand-copied into paper prose or tables.

Shared helper functions live in `diagnostics/lib_artifact.py`.

Run with Python 3 and the pinned numerical/plotting dependencies:

```bash
python3 -m venv /tmp/setstone-diagnostics
/tmp/setstone-diagnostics/bin/pip install -r diagnostics/requirements.txt
/tmp/setstone-diagnostics/bin/python diagnostics/finite_cohen.py
/tmp/setstone-diagnostics/bin/python diagnostics/definability_rarity.py
/tmp/setstone-diagnostics/bin/python diagnostics/hf_slice.py
```

HF rank bound `n` enumerates `V_(n+1)`, starting with `{empty}` at rank
bound zero. The JSON records both indices. The closure samples do not assert
that a bounded slice is a model closed under arbitrary pairing. Power-set
checks exhaust domains of rank at most 3; transport checks exhaust maps from
those domains into the four objects of rank at most 2.

Finite Cohen enumeration includes the empty lens and all surjective labeled
lenses for source sizes 1 through 5. Exact counts also check the block-splitting
product formula. Scaling tests use a binomial residual gate where expected
counts suffice; `observational_low_expected` cases have no statistical pass
criterion. These probabilities concern disagreement meeting, not full Cohen
genericity. The rarity companion gates its all-block splitting frequencies too.
