import Init.Omega

namespace SetStone
namespace CohenBoundary

/-! Choice-free infinite density lemmas and guards for the forcing bridge.
Conditions have a finite support bound, not an infinite set of assigned bits.
No ground model or forcing extension theorem is postulated here. -/

structure Condition where
  value : Nat -> Option Bool
  bound : Nat
  outside : forall n, bound <= n -> value n = none

def Extends (q p : Condition) : Prop :=
  forall n b, p.value n = some b -> q.value n = some b
def InG (h : Nat -> Bool) (p : Condition) : Prop :=
  forall n b, p.value n = some b -> h n = b
def Dense (D : Condition -> Prop) : Prop :=
  forall p, exists q, Extends q p /\ D q
def Meets (h : Nat -> Bool) (D : Condition -> Prop) : Prop :=
  exists p, InG h p /\ D p

def setAt (p : Condition) (n : Nat) (b : Bool) : Condition where
  value := fun k => if k = n then some b else p.value k
  bound := Nat.max p.bound (n + 1)
  outside := by
    intro k hk
    have hp : p.bound <= k := Nat.le_trans (Nat.le_max_left _ _) hk
    have hn : n + 1 <= k := Nat.le_trans (Nat.le_max_right _ _) hk
    have hne : k ≠ n := by omega
    simp [hne, p.outside k hp]

theorem setAt_self (p : Condition) (n : Nat) (b : Bool) :
    (setAt p n b).value n = some b := by simp [setAt]

theorem setAt_extends {p : Condition} {n : Nat} (hn : p.value n = none) (b : Bool) :
    Extends (setAt p n b) p := by
  intro k c hc
  by_cases hk : k = n
  · subst k
    rw [hn] at hc
    contradiction
  · simp [setAt, hk, hc]

theorem extends_trans {p q r : Condition} (hqr : Extends r q) (hpq : Extends q p) :
    Extends r p := fun n b hn => hqr n b (hpq n b hn)

def D (g : Nat -> Bool) (p : Condition) : Prop :=
  exists n b, p.value n = some b /\ b ≠ g n

theorem disagreement_dense (g : Nat -> Bool) : Dense (D g) := by
  intro p
  refine ⟨setAt p p.bound (!g p.bound), setAt_extends (p.outside _ (Nat.le_refl _)) _, ?_⟩
  exact ⟨p.bound, !g p.bound, setAt_self _ _ _, by cases g p.bound <;> decide⟩

theorem disagreement_meeting_iff (h g : Nat -> Bool) :
    Meets h (D g) <-> exists n, h n ≠ g n := by
  constructor
  · rintro ⟨p, hp, n, b, hn, hne⟩
    exact ⟨n, fun heq => hne ((hp n b hn).symm.trans heq)⟩
  · rintro ⟨n, hn⟩
    let empty : Condition := ⟨fun _ => none, 0, fun _ _ => rfl⟩
    refine ⟨setAt empty n (h n), ?_, n, h n, setAt_self _ _ _, hn⟩
    intro k b hk
    by_cases hkn : k = n
    · subst k
      simpa [setAt] using hk
    · simp [setAt, hkn, empty] at hk

def E (A : Nat -> Prop) (p : Condition) : Prop :=
  exists m n b c, A m /\ A n /\ p.value m = some b /\
    p.value n = some c /\ b ≠ c

theorem infinite_block_splitting_dense (A : Nat -> Prop)
    (hunbounded : forall bound, exists n, bound <= n /\ A n) : Dense (E A) := by
  intro p
  rcases hunbounded p.bound with ⟨m, hm, hAm⟩
  let q := setAt p m false
  rcases hunbounded q.bound with ⟨n, hn, hAn⟩
  have hmn : m ≠ n := by
    have hm1 : m + 1 <= q.bound := Nat.le_max_right _ _
    omega
  let r := setAt q n true
  refine ⟨r, extends_trans (setAt_extends (q.outside n hn) true)
    (setAt_extends (p.outside m hm) false), m, n, false, true, hAm, hAn, ?_,
    setAt_self q n true, by decide⟩
  simp [r, setAt, hmn, q]

/-! A dense family invisible to the disagreement/splitting-only criterion.
Every duplicated-bit real misses it, regardless of its other properties. -/
def PairMismatch (p : Condition) : Prop :=
  exists n b c, p.value (2 * n) = some b /\
    p.value (2 * n + 1) = some c /\ b ≠ c

theorem pairMismatch_dense : Dense PairMismatch := by
  intro p
  let n := p.bound
  have hfree : p.value (2 * n) = none := p.outside _ (by dsimp [n]; omega)
  let q := setAt p (2 * n) false
  have hfree' : q.value (2 * n + 1) = none := by
    change (if 2 * n + 1 = 2 * n then some false else p.value (2 * n + 1)) = none
    rw [if_neg (by omega)]
    exact p.outside _ (by dsimp [n]; omega)
  let r := setAt q (2 * n + 1) true
  refine ⟨r, extends_trans (setAt_extends hfree' true) (setAt_extends hfree false), ?_⟩
  refine ⟨n, false, true, ?_, setAt_self q _ _, by decide⟩
  change (if 2 * n = 2 * n + 1 then some true else q.value (2 * n)) = some false
  rw [if_neg (by omega)]
  exact setAt_self p _ false

def duplicate (r : Nat -> Bool) : Nat -> Bool := fun n => r (n / 2)

theorem duplicate_pairs_equal (r : Nat -> Bool) (n : Nat) :
    duplicate r (2 * n) = duplicate r (2 * n + 1) := by
  unfold duplicate
  congr 1 <;> omega

theorem duplicate_misses_dense (r : Nat -> Bool) : Not (Meets (duplicate r) PairMismatch) := by
  rintro ⟨p, hp, n, b, c, hb, hc, hne⟩
  exact hne ((hp _ _ hb).symm.trans
    ((duplicate_pairs_equal r n).trans (hp _ _ hc)))

/-! The ground-coded predicate family contains all singleton predicates.
If it were the full fiber-invariant predicate family of a map on Nat,
that map would be injective and every predicate would be visible. -/
def FiberVisible {X : Type} (f : Nat -> X) (h : Nat -> Bool) : Prop :=
  forall m n, f m = f n -> h m = h n

theorem singleton_visibility_forces_injective {X : Type} (f : Nat -> X)
    (hs : forall k, FiberVisible f (fun n => decide (n = k))) :
    forall m n, f m = f n -> m = n := by
  intro m n h
  have hb := hs m m n h
  have hn : decide (n = m) = true := by simpa using hb.symm
  exact (of_decide_eq_true hn).symm

theorem singleton_visibility_forces_all {X : Type} (f : Nat -> X)
    (hs : forall k, FiberVisible f (fun n => decide (n = k)))
    (h : Nat -> Bool) : FiberVisible f h := by
  intro m n heq
  rw [singleton_visibility_forces_injective f hs m n heq]

/-! A precise replacement for the invalid full-partition ground lens:
use a supplied predicate algebra, and adjoin a new predicate to it.
The bridge to an actual M is mathematical input, not an axiom of Lean. -/
structure BooleanClosed (B : (Nat -> Bool) -> Prop) : Prop where
  complement : forall h, B h -> B (fun n => !h n)
  intersection : forall h g, B h -> B g -> B (fun n => h n && g n)

inductive Adjoined (B : (Nat -> Bool) -> Prop) (x : Nat -> Bool) : (Nat -> Bool) -> Prop where
  | ground {h} : B h -> Adjoined B x h
  | new : Adjoined B x x
  | complement {h} : Adjoined B x h -> Adjoined B x (fun n => !h n)
  | intersection {h g} : Adjoined B x h -> Adjoined B x g ->
      Adjoined B x (fun n => h n && g n)

def StrictExtension (B C : (Nat -> Bool) -> Prop) : Prop :=
  (forall h, B h -> C h) /\ exists h, C h /\ Not (B h)

theorem adjoining_strict_iff_novel (B : (Nat -> Bool) -> Prop)
    (hB : BooleanClosed B) (x : Nat -> Bool) :
    StrictExtension B (Adjoined B x) <-> Not (B x) := by
  constructor
  · rintro ⟨_, h, hh, hnot⟩ hx
    have hall : forall g, Adjoined B x g -> B g := by
      intro g hg
      induction hg with
      | ground hb => exact hb
      | new => exact hx
      | complement _ ih => exact hB.complement _ ih
      | intersection _ _ ih jh => exact hB.intersection _ _ ih jh
    exact hnot (hall h hh)
  · intro hx
    exact ⟨fun _ hh => Adjoined.ground hh, x, Adjoined.new, hx⟩

end CohenBoundary
end SetStone
