# Six Birds: ZFC

This repository contains the **set-theory / foundations instantiation** for the paper:

> **To Set a Stone with Six Birds: The Free and Purchased Parts of ZFC**
>
> Version 2, 3 October 2026. DOI (v2): [10.5281/zenodo.23121590](https://doi.org/10.5281/zenodo.23121590)
>
> v1 (17 June 2026): [10.5281/zenodo.20712823](https://doi.org/10.5281/zenodo.20712823)
>
> Repository: https://github.com/ioannist/six-birds-zfc

This paper is the set-theoretic instantiation of the emergence calculus introduced in *Six Birds: Foundations of Emergence Calculus*. It shows that the Zermelo–Fraenkel axiom list **factors**, theorem by theorem, through a single staged construction discipline — packaging under a membership lens, audited by rank — and reads Gödel incompleteness and Cohen independence as the *saturation* and *extension* faces of that one discipline. The axioms separate into a **free** part (auditable from finite packaging) and a **purchased** part: four named, priced commitments (Infinity, Power set, Replacement, Choice) entered only through an explicit assumption box.

## What this repository provides

- **Manuscript source** under `paper/` — one LaTeX file per section (`paper/sections/`), appendices (`paper/appendices/`), shared macros (`paper/includes/`), generated tables/figures, and the bibliography `paper/references.bib`. Canonical build outputs under `paper/build/` (`main.pdf`, flattened `main_flat.tex`).
- **Lean theorem track** under `formal/` — the `SetStone` project (8 modules, ~1750 lines): `Packaging`, `HFClosure`, `HFSets`, `RankAudit`, `FiniteCohen`, `CohenBoundary`, `CohenRecognition`, `LiftChoice`. Mathlib-free, on a `{propext, Quot.sound}` axiom base with the Axiom of Choice (`Classical.choice`) absent throughout; `formal/AxiomAudit.lean` is a default build target that checks every project declaration (371, including private helpers) on each `lake build`.
- **Numerical diagnostics** under `diagnostics/` — falsification-first, deterministic seeded exhibits (`finite_cohen.py`, `definability_rarity.py`, `hf_slice.py`) that emit JSON runs (`results/`), TeX tables (`tables/`), and figures (`figures/`) the paper `\input{}`s.
- **Theorem inventory and paper contract** under `docs/spec/` (`theorem-inventory.md`, `paper-contract.md`).
- **Zenodo sync tooling** under `scripts/update_zenodo_cites.py` — updates the Zenodo deposition's `Cites` related-works from `paper/references.bib`.

## Scope and limitations

The paper is explicit about what it does and does not establish:

- It makes **no consistency claims** and claims **no new independence results**; every infinitary commitment is treated as a named, priced hypothesis.
- The free/purchased factorization and the finite forcing correspondence are in-house and Lean-backed over the **finite** setting; the infinitary `ZF(C)` shadow holds **conditionally**, under the assumption box and named classical imports.
- The Lean track mechanizes selected finite and structural cores, not the full manuscript; the theorems that *price* Choice are verified without using Choice.
- Countermodels guard the non-redundancy of each purchased commitment; they do not enlarge the free part.

## Build the paper

The canonical build is `latexmk` (configured by `paper/latexmkrc` to output into `paper/build/`):

```bash
cd paper && latexmk -pdf main.tex
```

Outputs:

- `paper/build/main.pdf`
- `paper/build/main_flat.tex`

## Build the Lean track

```bash
cd formal && lake build
```

Toolchain: `leanprover/lean4:4.28.0` (corpus pin), zero external requires (mathlib-free).

## Run the diagnostics

```bash
cd diagnostics && python finite_cohen.py && python definability_rarity.py && python hf_slice.py
```

Each script runs a deterministic seeded computation, writes `results/<name>_last_run.json`, regenerates `tables/<name>_table.tex`, and exits nonzero with a counterexample record if a falsification check fails.

## Update Zenodo related works

Set `ZENODO_ACCESS_TOKEN` in `.env` (git-ignored), then:

```bash
set -a; . ./.env; set +a
./scripts/update_zenodo_cites.py 10.5281/zenodo.23121590 paper/references.bib --offline   # parse only
./scripts/update_zenodo_cites.py 10.5281/zenodo.23121590 paper/references.bib              # Zenodo dry-run
./scripts/update_zenodo_cites.py 10.5281/zenodo.23121590 paper/references.bib --apply      # write draft metadata
```

## Repository notes

- Paper DOI: [10.5281/zenodo.20712823](https://doi.org/10.5281/zenodo.20712823)
- Active bibliography: `paper/references.bib`
- Canonical PDF: `paper/build/main.pdf`
- Flattened single-file TeX: `paper/build/main_flat.tex`
