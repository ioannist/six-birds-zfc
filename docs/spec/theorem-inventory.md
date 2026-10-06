# Theorem Inventory - To Set a Stone with Six Birds

Status vocabulary: `unattempted / drafted / sent_back / accepted / lean_validated / conditional_with_imports / blocked_at_external`.

This inventory is the live obligation ladder for the ZF track. Rows name targets and support deliverables; they do not record theorem acceptance until a manager-accepted step changes a status.

## Claim Ladder

| id | title | grade | status | depends_on | corpus_grounding | lean_surface | paper_section | nonclaim_pointer |
|---|---|---|---|---|---|---|---|---|
| D-ZF-01 | Set-theoretic theory package; membership instrument with extensional quotient and rank audit | in-house | drafted | Foundations II admissibility schemas; Foundations I theory-package vocabulary | research-plan Tier 0; Foundations I META primitives P5/P6 and theory package framing; Foundations II admissibility audit discipline | Supports `formal/SetStone/Packaging.lean`; no declaration yet | Instrument | `docs/spec/paper-contract.md` section 2 |
| T-ZF-00 | Mostowski collapse as P5 packaging; mathlib `PSet`/`ZFSet` quotient anchor | in-house | drafted | D-ZF-01; mathlib `PSet`/`ZFSet`; Foundations I idempotent endomap API | research-plan Tier 0; Foundations I P5 packaging; Foundations I closure/idempotent endomap note; mathlib quotient construction named in plan | `formal/SetStone/Packaging.lean` | Instrument | `docs/spec/paper-contract.md` section 2 |
| T-ZF-01 | HF closure under finite packaging, union, gated subpackaging, and descent transport | in-house | drafted | D-ZF-01; T-ZF-00; Foundations I closure saturation; A_FIN discipline | research-plan Tier 1; Foundations I Lemma `closure-iterate-stabilizes`; Corollary `closure-saturates`; finite induction spine | `formal/SetStone/HFClosure.lean` | Free part | `docs/spec/paper-contract.md` section 2 |
| T-ZF-02 | Infinity as forced package change; fixed finite completion does not reach an inductive set | in-house | drafted | T-ZF-01; Foundations I closure saturation; No-Go bounded-interface saturation; Incompleteness package-change bridge | research-plan Tier 1; Foundations I Corollary `closure-saturates`; Incompleteness `persistent_growth_witness_implies_package_change`; No-Go bounded-interface theorem | Possible surface in `formal/SetStone/HFClosure.lean`; no declaration yet | Free part | `docs/spec/paper-contract.md` section 2 |
| T-ZF-03 | Foundation as rank-audit exactness | in-house | drafted | D-ZF-01; well-founded staging; Foundations I P6 audit and exactness criterion | research-plan Tier 1; Foundations I P6 accounting; Foundations I Force Lives on Loops exactness/audit pattern; classical rank theorem cited for nonfinite scope | `formal/SetStone/RankAudit.lean` | Free part | `docs/spec/paper-contract.md` section 2 |
| C-INF | Inductive-stage completion source admitting the omega package | conditional-source | drafted | A-ZF assumption box; external dependency contract | research-plan A-ZF; Riemann recognition-source template; Incompleteness conditional-lift assumption box | Opaque commitment guard, module to be assigned under WP-7 | Assumption box | `docs/spec/paper-contract.md` sections 2 and 3 |
| C-POW | Full subpackage completion source admitting powersets per stage | conditional-source | drafted | A-ZF assumption box; external dependency contract | research-plan A-ZF; Riemann recognition-source template; Incompleteness conditional-lift assumption box | Opaque commitment guard, module to be assigned under WP-7 | Assumption box | `docs/spec/paper-contract.md` sections 2 and 3 |
| C-REPL | Unbounded descent-transport source for HL-META-1 images | conditional-source | drafted | A-ZF assumption box; external dependency contract; Foundations I HL-META-1 | research-plan A-ZF; Foundations I P1 descent condition HL-META-1; Riemann recognition-source template | Opaque commitment guard, module to be assigned under WP-7 | Assumption box | `docs/spec/paper-contract.md` sections 2 and 3 |
| C-SEL | Canonical-lift existence source for infinitary fibers | conditional-source | drafted | A-ZF assumption box; T-ZF-06; external AC equivalence | research-plan A-ZF and Tier 4; Foundations I downward-influence lift `U_f`; Riemann recognition-source template | Opaque commitment guard in `formal/SetStone/LiftChoice.lean` | Assumption box and Choice | `docs/spec/paper-contract.md` sections 2 and 3 |
| T-ZF-04 | Conditional shadow theorem for the staged hierarchy and its rank-erased membership shadow | conditional | drafted | C-INF; C-POW; C-REPL; C-SEL for the Choice extension; external dependency contract | research-plan Tier 2; Incompleteness conditional theorem ladder; Riemann assumption-box architecture; classical cumulative-hierarchy imports | Guarded conditional surface under WP-7; no declaration yet | Conditional shadow | `docs/spec/paper-contract.md` sections 2 and 3 |
| T-ZF-04a | Elementary translation theorem: rank-erasure preserves membership statements | in-house | drafted | D-ZF-01; staged/shadow syntax; T-ZF-04 setup | research-plan Tier 2; Riemann Theorem T template as zero-recognition bridge | Possible guarded bridge declaration under WP-7; no module assigned yet | Conditional shadow | `docs/spec/paper-contract.md` section 2 |
| T-ZF-05 | Forcing correspondence between Cohen extensions and SBT strict-theory extension | conditional | drafted | T-ZF-05f; external Cohen/Kunen forcing contract; Cantor non-factorization template | research-plan Tier 3; Foundations I finite forcing lemma and Nothing Stays Constant lemma; Cantor strict-extension theoremlet; Riemann external-contract pattern | No Lean target initially; finite core isolated in `formal/SetStone/FiniteCohen.lean` | Forcing correspondence | `docs/spec/paper-contract.md` sections 2 and 3 |
| T-ZF-05f | Finite Cohen bridge; finite density-meeting/block-splitting bridge and counting shadow | in-house | drafted | Foundations I A_FIN + A_LENS; finite forcing lemma; Nothing Stays Constant lemma | research-plan Tier 3 go/no-go gate; Foundations I `count-definable`, finite forcing lemma, Nothing Stays Constant lemma, strict-language-extension corollary | `formal/SetStone/FiniteCohen.lean` | Forcing finite core | `docs/spec/paper-contract.md` section 2 |
| T-ZF-05c | CH as lens relativity, scoped to host-bound model realizations | model | drafted | T-ZF-05; external Cohen/Kunen CH extension results | research-plan Tier 3; Cantor non-factorization template; external Cohen/Kunen forcing imports | No Lean target planned | Forcing worked instance | `docs/spec/paper-contract.md` sections 2 and 3 |
| T-ZF-06 | Choice as the cost of the lift `U_f`; finite lift and infinitary equivalence statement | in-house | drafted | Foundations I lift/completion `U_f`; C-SEL for infinitary commitment; external AC-product equivalence | research-plan Tier 4; Foundations I downward-influence representative selection via lift/completion; Riemann recognition-source guard pattern | `formal/SetStone/LiftChoice.lean` | Choice | `docs/spec/paper-contract.md` sections 2 and 3 |

## Countermodel Atlas

| id | title | grade | status | depends_on | corpus_grounding | lean_surface | paper_section | nonclaim_pointer |
|---|---|---|---|---|---|---|---|---|
| CM-ZF-1 | Quine atoms or non-extensional graph; blocks "extensionality is forced" | guard | drafted | D-ZF-01; T-ZF-00 | research-plan WP-4; Foundations III countermodel-atlas pattern; Foundations IV normal-form nonclaims | None planned | Countermodel atlas | `docs/spec/paper-contract.md` section 2 |
| CM-ZF-2 | Ill-founded membership graph; blocks "foundation is free without staging" | guard | drafted | T-ZF-03 | research-plan WP-4; Foundations I P6 exactness/audit pattern; Foundations III countermodel-atlas pattern | Possible finite graph diagnostic only; no theorem module assigned | Countermodel atlas | `docs/spec/paper-contract.md` section 2 |
| CM-ZF-3 | HF saturation witness; blocks "infinity emerges from fixed finite iteration" | guard | drafted | T-ZF-01; T-ZF-02 | research-plan WP-4; Foundations I closure saturation; Incompleteness fixed-package saturation | Possible support in `formal/SetStone/HFClosure.lean` | Countermodel atlas | `docs/spec/paper-contract.md` section 2 |
| CM-ZF-4 | Symmetric model sketch; blocks "the lift `U_f` is free infinitarily" | guard | drafted | T-ZF-06; C-SEL; external symmetric-model citation | research-plan WP-4; Foundations III countermodel-atlas pattern; Riemann external-contract discipline | None planned | Countermodel atlas | `docs/spec/paper-contract.md` sections 2 and 3 |
| CM-ZF-5 | `V_omega+omega` fragment; blocks "Replacement is implied by the other commitments" | guard | drafted | C-REPL; T-ZF-04; external model-fragment citation | research-plan WP-4; Incompleteness conditional-lift boundary; Riemann assumption-box nonclaim pattern | None planned | Countermodel atlas | `docs/spec/paper-contract.md` sections 2 and 3 |
| CM-ZF-6 | Definable-only predicate extension; blocks "every extension is strict" | guard | drafted | T-ZF-05; T-ZF-05f | research-plan WP-4; Foundations I definability and strict-language-extension corollary; Cantor strict-extension non-factorization template | Possible support in `formal/SetStone/FiniteCohen.lean` | Countermodel atlas | `docs/spec/paper-contract.md` section 2 |

## Lean Surface Rows

| id | title | grade | status | depends_on | corpus_grounding | lean_surface | paper_section | nonclaim_pointer |
|---|---|---|---|---|---|---|---|---|
| formal/SetStone/Packaging.lean | Packaging module for T-ZF-00 and commitment guards | organizational | lean_validated | D-ZF-01; T-ZF-00; A-ZF guard rows | research-plan WP-7; Foundations I `ClosureLadder/Basic.lean` note; mathlib `PSet`/`ZFSet` anchor named in plan | `formal/SetStone/Packaging.lean` | Lean appendix | `docs/spec/paper-contract.md` section 2 |
| formal/SetStone/HFClosure.lean | HF closure module for finite free-part fragments | organizational | lean_validated | T-ZF-01; T-ZF-02; CM-ZF-3 | research-plan WP-7; Foundations I closure saturation API; finite induction route in plan | `formal/SetStone/HFClosure.lean` | Lean appendix | `docs/spec/paper-contract.md` section 2 |
| formal/SetStone/RankAudit.lean | Rank-audit module for finite/HF Foundation instances | organizational | lean_validated | T-ZF-03; CM-ZF-2 | research-plan WP-7; Foundations I P6 audit and exactness pattern; Foundations IV law template | `formal/SetStone/RankAudit.lean` | Lean appendix | `docs/spec/paper-contract.md` section 2 |
| formal/SetStone/FiniteCohen.lean | Finite Cohen bridge module | organizational | lean_validated | T-ZF-05f; CM-ZF-6 | research-plan WP-7; Foundations I finite forcing lemma, `count-definable`, Nothing Stays Constant lemma | `formal/SetStone/FiniteCohen.lean` | Lean appendix | `docs/spec/paper-contract.md` section 2 |
| formal/SetStone/LiftChoice.lean | Lift/Choice module for finite lift and AC-product equivalence surface | organizational | lean_validated | T-ZF-06; C-SEL; CM-ZF-4 | research-plan WP-7; Foundations I lift/completion `U_f`; external AC-product equivalence | `formal/SetStone/LiftChoice.lean` | Lean appendix | `docs/spec/paper-contract.md` sections 2 and 3 |

## Diagnostics Rows

| id | title | grade | status | depends_on | corpus_grounding | lean_surface | paper_section | nonclaim_pointer |
|---|---|---|---|---|---|---|---|---|
| HF-slice axiom checks | Enumerate HF by rank and check finite Tier-1 axiom fragments on slices | finite-diagnostic | accepted | T-ZF-01; T-ZF-03 | research-plan WP-8; To Count a Stone falsification-first diagnostics; Foundations III manifest-driven evidence pattern | Generated diagnostics only; no Lean declaration | Diagnostics appendix | `docs/spec/paper-contract.md` section 2 |
| definability-rarity statistics | Sample predicate adjunctions and compare definability rarity to the finite counting prediction | finite-diagnostic | accepted | Foundations I `count-definable`; T-ZF-05f | research-plan WP-8; Foundations I finite forcing lemma and strict-language-extension corollary; To Count a Stone run-artifact contract | Generated diagnostics only; no Lean declaration | Diagnostics appendix | `docs/spec/paper-contract.md` section 2 |
| finite Cohen simulation | Verify finite density-meeting versus block-splitting on sampled finite lenses | finite-diagnostic | accepted | T-ZF-05f | research-plan WP-8; Foundations I Nothing Stays Constant lemma; finite Cohen bridge target in plan | Generated diagnostics only; no Lean declaration | Diagnostics appendix | `docs/spec/paper-contract.md` section 2 |

## Change Discipline

Only manager-accepted verdicts change statuses in this inventory. Every status change must cite the step number that caused it and must preserve the declared status vocabulary.

## Status changelog

| date | id | change | step |
|---|---|---|---|
| 2026-06-10 | T-ZF-05f | unattempted → drafted (statement + full proofs accepted at .tex level; Lean pending) | step 2 |
| 2026-06-10 | D-ZF-01 | unattempted → drafted (definitions + L1/L2/L3 proved; admissibility table) | step 3 |
| 2026-06-10 | T-ZF-00 | unattempted → drafted (idempotence, Fix ≅ HF, P5 quotient, finite Mostowski; mathlib anchor doc-verified) | step 4 |
| 2026-06-10 | T-ZF-01 | unattempted → drafted (packaging operator, cl_F(∅)=HF, ZF−Inf satisfaction; one send-back for HF-transitivity/absoluteness fix, revised and accepted) | step 5 |
| 2026-06-10 | T-ZF-02 | unattempted → drafted (finitely generated rule class, HF-stability, non-attainment, package-change corollary; F̂ ambient sharpening) | step 6 |
| 2026-06-10 | T-ZF-03 | unattempted → drafted (finite TFAE, set-level corollary, cycle witnesses for CM-ZF-2, headline reading) | step 7 |
| 2026-06-10 | T-ZF-04a | unattempted → drafted (reduct lemma; Ord + rank-graph FO-definability over (HF,∈); lossless translation; one send-back for unnesting lemma) | step 8 |
| 2026-06-10 | T-ZF-06 | unattempted → drafted (finite lift no-choice; section reading; ZF-metatheoretic 4-way equivalence with scope flag; C-SEL headline) | step 9 |
| 2026-06-10 | C-INF/C-POW/C-REPL/C-SEL | unattempted → drafted (A-ZF box: precise forms, pricing, opacity-guard specs, dependency manifest) | step 10 |
| 2026-06-10 | T-ZF-04 | unattempted → drafted (conditional_theorem_with_named_imports: imports register I1–I6, supplier ledger, factorization table, per-grade non-redundancy) | step 11 |
| 2026-06-10 | CM-ZF-1/2/3/6 | unattempted → drafted (atlas part 1: in-situ witnesses incl. lens non-injectivity and trivial-extension construction) | step 12 |
| 2026-06-10 | CM-ZF-4/5 | unattempted → drafted (atlas part 2: citation-grade purchase guards; H_ω1 wording flagged to-verify at prose) | step 13 |
| 2026-06-11 | T-ZF-05 | unattempted → drafted (conditional_with_named_imports J1/J2: in-house RS lemma, genericity=non-definability via T-ZF-05f densities, non-factorization, correspondence table) | step 15 |
| 2026-06-11 | T-ZF-05c | unattempted → drafted (model_instance_complete: Gödel/Cohen cited in relative form; lens-relativity package reading) | step 16 |
| 2026-06-11 | FiniteCohen.lean | unattempted → lean_validated (mathlib-free; meet_D/E equivalences + density-defect F_D/F_E characterizations; sorry-free; axioms propext+Quot.sound only) | step 17 |
| 2026-06-11 | T-ZF-05f | drafted → note: combinatorial core (i)/(ii) machine-checked in FiniteCohen.lean; counting shadow (iii) stays paper-only | step 17 |
| 2026-06-11 | HFClosure.lean | unattempted → lean_validated (recursive extensional Equiv via WF-recursion on height; pair/union/derived-collect membership; mem_rank_lt; one send-back for faithfulness) | step 18 |
| 2026-06-11 | RankAudit.lean | unattempted → lean_validated (potential excludes self-loop/cycle; minimal-element; concrete self-loop & 2-cycle witnesses no-potential; acyclic⇒potential left paper-only) | step 19 |
| 2026-06-11 | Packaging.lean | unattempted → lean_validated (idempotents-split: Fix=Image, r∘i=id, i∘r=e, fully axiom-free; concrete collapseFin3 witness; concrete E + ZFSet anchor paper-only) | step 20 |
| 2026-06-11 | LiftChoice.lean | unattempted → lean_validated (finite section choice-free via List.find? search; section⟺prototype; concrete Fin4→Fin2 witness; infinitary AC equiv paper-only by nature) | step 21 |
| 2026-06-11 | finite Cohen simulation | unattempted → accepted (Part A: exhaustive cross-check of all 4 FiniteCohen theorems over 633 lenses / millions of instances, all pass; Part B: P(meets every D_g)=1-2^-(N-K)→1 matching to ~4 dp; figure) | step 24 |
| 2026-06-11 | definability-rarity statistics | unattempted → accepted (9 configs N-K=0..20; empirical matches 2^-(N-K), 7 z-gated |z|≤4, N=K exact, tiny-prob observational; figure; all_passed) | step 23 |
| 2026-06-11 | HF-slice axiom checks | unattempted → accepted (V_0..V_4 enumerated = 1,2,4,16,65536; C1-C7 falsification checks pass, C6/C7 exhaustive over V_4; artifact contract enforced) | step 22 |
| 2026-06-11 | Lean track (all 5 modules) | SIGNED OFF — manager audit: clean-room build, deep hygiene, 29-theorem axiom audit ([propext, Quot.sound] max, 6 axiom-free, no Classical.choice), full faithfulness re-read | sign-off |
