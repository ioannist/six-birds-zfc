import SetStone.HFClosure

namespace SetStone
namespace HFSets

/-! Actual extensional HF objects, constructed without selecting representatives.
This is the quotient of finite trees, not a formalization of arbitrary finite
DAGs or the infinitary universe. All operations descend by proved congruence. -/

open HFClosure

def hfSetoid : Setoid HF where
  r := Equiv
  iseqv := ⟨equiv_refl, equiv_symm, fun {a b c} => equiv_trans a b c⟩

def Set := Quotient hfSetoid
def ofHF (a : HF) : Set := Quotient.mk hfSetoid a

theorem ofHF_eq_iff (a b : HF) : ofHF a = ofHF b <-> Equiv a b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := hfSetoid) h⟩

def mem (a b : Set) : Prop :=
  Quotient.liftOn₂ a b Mem (by
    intro a b a' b' ha hb
    apply propext
    exact (mem_congr_left ha).trans (mem_congr_right hb))

theorem mem_ofHF (a b : HF) : mem (ofHF a) (ofHF b) <-> Mem a b := Iff.rfl

theorem ext (a b : Set) (h : forall c, mem c a <-> mem c b) : a = b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      apply Quotient.sound
      apply (equiv_iff_mem a b).mpr
      intro c
      exact h (ofHF c)

def empty : Set := ofHF emptyHF

theorem not_mem_empty (a : Set) : Not (mem a empty) := by
  induction a using Quotient.inductionOn with
  | h a => exact not_mem_emptyHF a

def pair (a b : Set) : Set :=
  Quotient.liftOn₂ a b (fun a b => ofHF (pairHF a b)) (by
    intro a b a' b' ha hb
    exact Quotient.sound (pairHF_congr ha hb))

theorem mem_pair (a b c : Set) : mem c (pair a b) <-> (c = a \/ c = b) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      induction c using Quotient.inductionOn with
      | h c =>
        change Mem c (pairHF a b) <-> (ofHF c = ofHF a \/ ofHF c = ofHF b)
        rw [mem_pairHF_iff, ofHF_eq_iff, ofHF_eq_iff]

def union (a : Set) : Set :=
  Quotient.liftOn a (fun a => ofHF (unionHF a)) (by
    intro a b h
    exact Quotient.sound (unionHF_congr h))

theorem mem_union (a c : Set) :
    mem c (union a) <-> exists d, mem d a /\ mem c d := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction c using Quotient.inductionOn with
    | h c =>
      constructor
      · intro h
        rcases (mem_unionHF_iff a c).mp h with ⟨d, hd, hc⟩
        exact ⟨ofHF d, hd, hc⟩
      · rintro ⟨d, hd, hc⟩
        induction d using Quotient.inductionOn with
        | h d => exact (mem_unionHF_iff a c).mpr ⟨d, hd, hc⟩

def rank (a : Set) : Nat :=
  Quotient.liftOn a HFClosure.rank (by
    intro a b h
    exact rank_eq_of_equiv h)

/-! Decidable gates must be invariant under extensional equality.
Taking the gate on the quotient supplies that invariance automatically. -/
def separate (p : Set -> Bool) (a : Set) : Set :=
  Quotient.liftOn a (fun a => ofHF (filterHF (fun x => p (ofHF x)) a)) (by
    intro a b hab
    apply Quotient.sound
    apply filterHF_congr _ _ hab
    intro x y hxy
    exact congrArg p (Quotient.sound (s := hfSetoid) hxy))

theorem mem_separate (p : Set -> Bool) (a c : Set) :
    mem c (separate p a) <-> (mem c a /\ p c = true) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction c using Quotient.inductionOn with
    | h c =>
      apply mem_filterHF_iff
      intro x y hxy
      exact congrArg p (Quotient.sound (s := hfSetoid) hxy)

theorem mem_rank_lt {a b : Set} (h : mem a b) : rank a < rank b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b => exact HFClosure.mem_rank_lt h

theorem not_mem_self (a : Set) : Not (mem a a) := by
  intro h
  exact Nat.lt_irrefl _ (mem_rank_lt h)

def succ (a : Set) : Set := union (pair a (pair a a))
def InductiveSet (a : Set) : Prop :=
  mem empty a /\ forall x, mem x a -> mem (succ x) a

theorem no_inductive_set (a : Set) : Not (InductiveSet a) := by
  induction a using Quotient.inductionOn with
  | h a =>
    intro h
    apply not_inductiveHF a
    exact ⟨h.1, fun x hx => h.2 (ofHF x) hx⟩

theorem closed_family_all (A : Set -> Prop) (he : A empty)
    (hp : forall a b, A a -> A b -> A (pair a b))
    (hu : forall a, A a -> A (union a)) : forall a, A a := by
  have hc : ClosedFamily (fun a => A (ofHF a)) := {
    respects := by
      intro a b hab ha
      have heq : ofHF a = ofHF b := Quotient.sound hab
      rw [← heq]
      exact ha
    empty := he
    pair := fun {a b} ha hb => hp (ofHF a) (ofHF b) ha hb
    union := fun {a} ha => hu (ofHF a) ha
  }
  intro a
  induction a using Quotient.inductionOn with
  | h a => exact closed_contains_all hc a

end HFSets
end SetStone
