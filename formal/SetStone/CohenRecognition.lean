import SetStone.CohenBoundary

namespace SetStone
namespace CohenRecognition

open CohenBoundary

/-! An exact recognition bridge, separate from mere predicate novelty.

`Condition` presents a finite partial assignment with a support bound; equal
assignments may have different bounds. Cylinders and all constructions here
use only the assignments and the extension relation, not bound equality.

A tree code permits partial assignments and is downward closed under taking
restrictions. Its closed branch set consists of total reals all of whose finite
restrictions are permitted. The complement is a union of finite cylinders.
For each dense requirement, we construct its obstruction tree and prove it
nowhere dense. The converse recognition implication uses a named classical
dichotomy, supplied as a premise rather than imported via Classical.choice.
Ground-model code membership and coverage of all its dense sets are external
inputs; this module does not invent or axiomatize a transitive ground model.
-/

def Tree (T : Condition -> Prop) : Prop :=
  forall p q, Extends q p -> T q -> T p

def Branch (T : Condition -> Prop) (h : Nat -> Bool) : Prop :=
  forall p, InG h p -> T p

def NowhereDense (T : Condition -> Prop) : Prop :=
  forall p, exists q, Extends q p /\ Not (T q)

def OpenCover (D : Condition -> Prop) (p : Condition) : Prop :=
  exists q, Extends p q /\ D q

def Obstruction (D : Condition -> Prop) (p : Condition) : Prop :=
  Not (OpenCover D p)

def prefixCondition (h : Nat -> Bool) (length : Nat) : Condition where
  value := fun n => if n < length then some (h n) else none
  bound := length
  outside := by
    intro n hn
    exact if_neg (Nat.not_lt_of_ge hn)

theorem prefix_inG (h : Nat -> Bool) (length : Nat) : InG h (prefixCondition h length) := by
  intro n b hn
  by_cases hlt : n < length
  · have hb : some (h n) = some b := by simpa only [prefixCondition, if_pos hlt] using hn
    exact Option.some.inj hb
  · have hb : (none : Option Bool) = some b := by
      simpa only [prefixCondition, if_neg hlt] using hn
    cases hb

theorem prefix_extends_restriction (h : Nat -> Bool) (p : Condition) (hp : InG h p) :
    Extends (prefixCondition h p.bound) p := by
  intro n b hn
  have hlt : n < p.bound := by
    by_cases hlt : n < p.bound
    · exact hlt
    · have ho : p.value n = none := p.outside n (Nat.le_of_not_lt hlt)
      rw [ho] at hn
      cases hn
  change (if n < p.bound then some (h n) else none) = some b
  rw [if_pos hlt, hp n b hn]

theorem branch_iff_prefixes (T : Condition -> Prop) (hT : Tree T) (h : Nat -> Bool) :
    Branch T h <-> forall length, T (prefixCondition h length) := by
  constructor
  · intro hb length
    exact hb _ (prefix_inG h length)
  · intro hs p hp
    exact hT p (prefixCondition h p.bound) (prefix_extends_restriction h p hp) (hs p.bound)

theorem nowhereDense_cylinder (T : Condition -> Prop) (hT : NowhereDense T) :
    forall p, exists q, Extends q p /\
      forall h, InG h q -> Not (Branch T h) := by
  intro p
  rcases hT p with ⟨q, he, hq⟩
  exact ⟨q, he, fun h hh hb => hq (hb q hh)⟩

theorem extends_refl (p : Condition) : Extends p p := fun _ _ h => h

theorem inG_of_extends {h : Nat -> Bool} {p q : Condition}
    (hq : InG h q) (he : Extends q p) : InG h p :=
  fun n b hb => hq n b (he n b hb)

theorem openCover_upward (D : Condition -> Prop) {p q : Condition}
    (he : Extends q p) (hp : OpenCover D p) : OpenCover D q := by
  rcases hp with ⟨r, hpr, hr⟩
  exact ⟨r, extends_trans he hpr, hr⟩

theorem obstruction_tree (D : Condition -> Prop) : Tree (Obstruction D) := by
  intro p q he hq hp
  exact hq (openCover_upward D he hp)

theorem obstruction_nowhereDense (D : Condition -> Prop) (hd : Dense D) :
    NowhereDense (Obstruction D) := by
  intro p
  rcases hd p with ⟨q, he, hq⟩
  exact ⟨q, he, fun hT => hT ⟨q, extends_refl q, hq⟩⟩

theorem meets_openCover_iff (h : Nat -> Bool) (D : Condition -> Prop) :
    Meets h (OpenCover D) <-> Meets h D := by
  constructor
  · rintro ⟨p, hp, q, he, hq⟩
    exact ⟨q, inG_of_extends hp he, hq⟩
  · rintro ⟨p, hp, hd⟩
    exact ⟨p, hp, p, extends_refl p, hd⟩

theorem branch_obstruction_iff_not_meets (h : Nat -> Bool) (D : Condition -> Prop) :
    Branch (Obstruction D) h <-> Not (Meets h D) := by
  constructor
  · intro hb hm
    rcases hm with ⟨p, hp, hd⟩
    exact hb p hp ⟨p, extends_refl p, hd⟩
  · intro hm p hp hcover
    exact hm ((meets_openCover_iff h D).mp ⟨p, hp, hcover⟩)

theorem meets_iff_avoids_obstruction (h : Nat -> Bool) (D : Condition -> Prop)
    (hlogic : Meets h D \/ Not (Meets h D)) :
    Meets h D <-> Not (Branch (Obstruction D) h) := by
  constructor
  · intro hm hb
    exact (branch_obstruction_iff_not_meets h D).mp hb hm
  · intro hb
    cases hlogic with
    | inl hm => exact hm
    | inr hn => exact False.elim (hb ((branch_obstruction_iff_not_meets h D).mpr hn))

def MeetsAll {I : Type} (requirements : I -> Condition -> Prop) (h : Nat -> Bool) : Prop :=
  forall i, Meets h (requirements i)

theorem meetsAll_iff_avoids_obstructions {I : Type}
    (requirements : I -> Condition -> Prop) (h : Nat -> Bool)
    (hlogic : forall i, Meets h (requirements i) \/ Not (Meets h (requirements i))) :
    MeetsAll requirements h <-> forall i, Not (Branch (Obstruction (requirements i)) h) := by
  constructor
  · intro hm i
    exact (meets_iff_avoids_obstruction h (requirements i) (hlogic i)).mp (hm i)
  · intro ha i
    exact (meets_iff_avoids_obstruction h (requirements i) (hlogic i)).mpr (ha i)

/-! The stronger characterization detects the actual counterexample.
It does not erase the gap between disagreement/splitting and genericity. -/
theorem duplicated_real_in_obstruction (r : Nat -> Bool) :
    Branch (Obstruction PairMismatch) (duplicate r) :=
  (branch_obstruction_iff_not_meets _ _).mpr (duplicate_misses_dense r)

theorem pairMismatch_obstruction_nowhereDense : NowhereDense (Obstruction PairMismatch) :=
  obstruction_nowhereDense _ pairMismatch_dense

/-! Both adopted repair routes in one explicit scope.

`coded` records the ground-coded condition families. Interpreting it for an
actual ground model remains an external bridge. To replace the full register
by an indexed family, `hentries` and `hcoverage` certify both directions of
coverage; checking only disagreement or splitting families cannot satisfy
that requirement for the intended ground model.
-/
def GenericRelative (coded : (Condition -> Prop) -> Prop) (h : Nat -> Bool) : Prop :=
  forall D, coded D -> Dense D -> Meets h D

theorem registered_pairMismatch_excludes_duplicate
    (coded : (Condition -> Prop) -> Prop) (hcode : coded PairMismatch) (r : Nat -> Bool) :
    Not (GenericRelative coded (duplicate r)) := by
  intro hg
  exact duplicate_misses_dense r (hg PairMismatch hcode pairMismatch_dense)

theorem generic_iff_meets_complete_family {I : Type}
    (coded : (Condition -> Prop) -> Prop) (requirements : I -> Condition -> Prop)
    (hentries : forall i, coded (requirements i) /\ Dense (requirements i))
    (hcoverage : forall D, coded D -> Dense D -> exists i, requirements i = D)
    (h : Nat -> Bool) : GenericRelative coded h <-> MeetsAll requirements h := by
  constructor
  · intro hg i
    exact hg (requirements i) (hentries i).1 (hentries i).2
  · intro hm D hc hd
    rcases hcoverage D hc hd with ⟨i, hi⟩
    rw [← hi]
    exact hm i

theorem generic_implies_novel (coded : (Condition -> Prop) -> Prop)
    (B : (Nat -> Bool) -> Prop)
    (hground : forall g, B g -> coded (D g))
    (h : Nat -> Bool) (hg : GenericRelative coded h) : Not (B h) := by
  intro hh
  have hm := hg (D h) (hground h hh) (disagreement_dense h)
  rcases (disagreement_meeting_iff h h).mp hm with ⟨n, hne⟩
  exact hne rfl

theorem generic_implies_strict_extension (coded : (Condition -> Prop) -> Prop)
    (B : (Nat -> Bool) -> Prop) (hB : BooleanClosed B)
    (hground : forall g, B g -> coded (D g))
    (h : Nat -> Bool) (hg : GenericRelative coded h) :
    StrictExtension B (Adjoined B h) :=
  (adjoining_strict_iff_novel B hB h).mpr (generic_implies_novel coded B hground h hg)

theorem forcing_repair_both {I : Type}
    (coded : (Condition -> Prop) -> Prop) (requirements : I -> Condition -> Prop)
    (hentries : forall i, coded (requirements i) /\ Dense (requirements i))
    (hcoverage : forall D, coded D -> Dense D -> exists i, requirements i = D)
    (B : (Nat -> Bool) -> Prop) (hB : BooleanClosed B)
    (hground : forall g, B g -> coded (D g)) (h : Nat -> Bool)
    (hlogic : forall i, Meets h (requirements i) \/ Not (Meets h (requirements i))) :
    (forall i, NowhereDense (Obstruction (requirements i))) /\
    (GenericRelative coded h <-> forall i, Not (Branch (Obstruction (requirements i)) h)) /\
    (GenericRelative coded h -> StrictExtension B (Adjoined B h)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact obstruction_nowhereDense (requirements i) (hentries i).2
  · exact (generic_iff_meets_complete_family coded requirements hentries hcoverage h).trans
      (meetsAll_iff_avoids_obstructions requirements h hlogic)
  · exact generic_implies_strict_extension coded B hB hground h

end CohenRecognition
end SetStone
