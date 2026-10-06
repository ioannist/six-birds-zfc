namespace SetStone
namespace LiftChoice

/-!
Mathlib-free finite lift core for T-ZF-06.

For a surjective finite lens `f : Fin N -> Fin K`, this module builds a
section by explicit finite search through `List.finRange N`.
-/

def Surj {N K : Nat} (f : Fin N -> Fin K) : Prop :=
  forall x, exists z, f z = x

def InFiber {N K : Nat} (f : Fin N -> Fin K) (x : Fin K) (z : Fin N) : Prop :=
  f z = x

def IsSection {N K : Nat} (f : Fin N -> Fin K) (s : Fin K -> Fin N) : Prop :=
  forall x, f (s x) = x

def PrototypeFamily {N K : Nat} (f : Fin N -> Fin K) (s : Fin K -> Fin N) : Prop :=
  forall x, InFiber f x (s x)

def searchPreimage {N K : Nat} (f : Fin N -> Fin K) (x : Fin K) : Option (Fin N) :=
  List.find? (fun z => decide (f z = x)) (List.finRange N)

theorem searchPreimage_isSome {N K : Nat} {f : Fin N -> Fin K}
    (hs : Surj f) (x : Fin K) :
    (searchPreimage f x).isSome = true := by
  unfold searchPreimage
  rw [List.find?_isSome]
  rcases hs x with ⟨z, hz⟩
  exact ⟨z, List.mem_finRange z, decide_eq_true hz⟩

def findPreimage {N K : Nat} (f : Fin N -> Fin K) (hs : Surj f) (x : Fin K) : Fin N :=
  Option.get (searchPreimage f x) (searchPreimage_isSome hs x)

theorem option_eq_some_get {A : Type} (o : Option A) (h : o.isSome = true) :
    o = some (Option.get o h) := by
  cases o with
  | none =>
      cases h
  | some _ =>
      rfl

theorem findPreimage_spec {N K : Nat} (f : Fin N -> Fin K) (hs : Surj f) (x : Fin K) :
    f (findPreimage f hs x) = x := by
  unfold findPreimage
  have hsome := searchPreimage_isSome (f := f) hs x
  have hopt : searchPreimage f x = some (Option.get (searchPreimage f x) hsome) :=
    option_eq_some_get (searchPreimage f x) hsome
  unfold searchPreimage at hopt
  have hp := List.find?_some (p := fun z => decide (f z = x)) (l := List.finRange N) hopt
  exact of_decide_eq_true hp

theorem finite_section_exists {N K : Nat} (f : Fin N -> Fin K) :
    Surj f -> exists s : Fin K -> Fin N, IsSection f s := by
  intro hs
  exact ⟨findPreimage f hs, findPreimage_spec f hs⟩

theorem section_iff_prototype {N K : Nat} (f : Fin N -> Fin K) (s : Fin K -> Fin N) :
    IsSection f s <-> PrototypeFamily f s := by
  unfold IsSection PrototypeFamily InFiber
  exact Iff.rfl

def concreteLens : Fin 4 -> Fin 2 :=
  fun k =>
    if k = (0 : Fin 4) then (0 : Fin 2)
    else if k = (1 : Fin 4) then (0 : Fin 2)
    else (1 : Fin 2)

def concreteSection : Fin 2 -> Fin 4 :=
  fun x => if x = (0 : Fin 2) then (0 : Fin 4) else (2 : Fin 4)

theorem concrete_section_property : IsSection concreteLens concreteSection := by
  intro x
  refine Fin.cases ?zero ?succ x
  · decide
  · intro i
    refine Fin.cases ?one ?impossible i
    · decide
    · intro j
      exact Fin.elim0 j

theorem concreteLens_surj : Surj concreteLens := by
  intro x
  refine Fin.cases ?zero ?succ x
  · exact ⟨(0 : Fin 4), by decide⟩
  · intro i
    refine Fin.cases ?one ?impossible i
    · exact ⟨(2 : Fin 4), by decide⟩
    · intro j
      exact Fin.elim0 j

theorem concrete_section_is_prototype : PrototypeFamily concreteLens concreteSection := by
  exact (section_iff_prototype concreteLens concreteSection).mp concrete_section_property

end LiftChoice
end SetStone
