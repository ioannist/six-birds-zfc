import Init.Omega

namespace SetStone
namespace RankAudit

/-!
Mathlib-free finite rank-audit core for T-ZF-03.

Graphs are finite directed graphs on `Fin N`, represented by an edge
predicate.  This module validates the audit-potential directions and
the two cycle witnesses used by the paper's finite TFAE theorem.
-/

def Decreasing {N : Nat} (Edge : Fin N -> Fin N -> Prop) (rho : Fin N -> Nat) : Prop :=
  forall u w, Edge u w -> rho w < rho u

def HasPotential {N : Nat} (Edge : Fin N -> Fin N -> Prop) : Prop :=
  exists rho, Decreasing Edge rho

def WalkList {N : Nat} (Edge : Fin N -> Fin N -> Prop) :
    Fin N -> List (Fin N) -> Fin N -> Prop
  | u, [], v => u = v
  | u, w :: rest, v => Edge u w /\ WalkList Edge w rest v

def IsCycle {N : Nat} (Edge : Fin N -> Fin N -> Prop) (start : Fin N)
    (rest : List (Fin N)) : Prop :=
  rest ≠ [] /\ WalkList Edge start rest start

theorem walkList_potential_le {N : Nat} {Edge : Fin N -> Fin N -> Prop}
    {rho : Fin N -> Nat} (hdec : Decreasing Edge rho) :
    forall rest u v, WalkList Edge u rest v -> rho v <= rho u
  | [], u, v, h => by
      cases h
      exact Nat.le_refl (rho u)
  | w :: rest, u, v, h => by
      have hedge : Edge u w := h.1
      have hwalk : WalkList Edge w rest v := h.2
      have htail : rho v <= rho w := walkList_potential_le hdec rest w v hwalk
      have hstep : rho w < rho u := hdec u w hedge
      exact Nat.le_trans htail (Nat.le_of_lt hstep)

theorem potential_excludes_self_loop {N : Nat} {Edge : Fin N -> Fin N -> Prop}
    (hpot : HasPotential Edge) (u : Fin N) : Not (Edge u u) := by
  intro hself
  rcases hpot with ⟨rho, hdec⟩
  have hlt : rho u < rho u := hdec u u hself
  exact (Nat.lt_irrefl (rho u)) hlt

theorem potential_excludes_cycle {N : Nat} {Edge : Fin N -> Fin N -> Prop}
    (hpot : HasPotential Edge) {start : Fin N} {rest : List (Fin N)} :
    Not (IsCycle Edge start rest) := by
  intro hcycle
  rcases hpot with ⟨rho, hdec⟩
  cases rest with
  | nil =>
      exact hcycle.1 rfl
  | cons w tail =>
      have hedge : Edge start w := hcycle.2.1
      have hwalk : WalkList Edge w tail start := hcycle.2.2
      have hle : rho start <= rho w := walkList_potential_le hdec tail w start hwalk
      have hlt : rho w < rho start := hdec start w hedge
      exact (Nat.not_lt_of_ge hle) hlt

theorem exists_min_rho_cons {N : Nat} (rho : Fin N -> Nat) :
    forall x xs,
      exists m, m ∈ x :: xs /\ forall s, s ∈ x :: xs -> rho m <= rho s
  | x, [] => by
      exact ⟨x, List.Mem.head [], by
        intro s hs
        cases hs with
        | head =>
            exact Nat.le_refl (rho x)
        | tail _ hnil =>
            cases hnil⟩
  | x, y :: ys => by
      rcases exists_min_rho_cons rho y ys with ⟨m, hmem, hmin⟩
      by_cases hxm : rho x <= rho m
      · exact ⟨x, List.Mem.head (y :: ys), by
          intro s hs
          cases hs with
          | head =>
              exact Nat.le_refl (rho x)
          | tail _ htail =>
              exact Nat.le_trans hxm (hmin s htail)⟩
      · have hmx : rho m <= rho x := by omega
        exact ⟨m, List.Mem.tail x hmem, by
          intro s hs
          cases hs with
          | head =>
              exact hmx
          | tail _ htail =>
              exact hmin s htail⟩

theorem min_of_potential {N : Nat} {Edge : Fin N -> Fin N -> Prop}
    (hpot : HasPotential Edge) {S : List (Fin N)} (hne : S ≠ []) :
    exists m, m ∈ S /\ forall s, s ∈ S -> Not (Edge m s) := by
  rcases hpot with ⟨rho, hdec⟩
  cases S with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      rcases exists_min_rho_cons rho x xs with ⟨m, hmem, hmin⟩
      exact ⟨m, hmem, by
        intro s hs hedge
        have hlt : rho s < rho m := hdec m s hedge
        have hle : rho m <= rho s := hmin s hs
        exact (Nat.not_lt_of_ge hle) hlt⟩

def SelfLoopEdge : Fin 1 -> Fin 1 -> Prop :=
  fun _ _ => True

theorem self_loop_is_cycle : IsCycle SelfLoopEdge (0 : Fin 1) [(0 : Fin 1)] := by
  constructor
  · intro h
    cases h
  · constructor
    · trivial
    · rfl

theorem self_loop_no_potential : Not (HasPotential SelfLoopEdge) := by
  intro hpot
  exact potential_excludes_self_loop hpot (0 : Fin 1) trivial

def TwoCycleEdge : Fin 2 -> Fin 2 -> Prop :=
  fun u v => (u = (0 : Fin 2) /\ v = (1 : Fin 2)) \/
    (u = (1 : Fin 2) /\ v = (0 : Fin 2))

theorem two_cycle_is_cycle : IsCycle TwoCycleEdge (0 : Fin 2) [(1 : Fin 2), (0 : Fin 2)] := by
  constructor
  · intro h
    cases h
  · constructor
    · exact Or.inl ⟨rfl, rfl⟩
    · constructor
      · exact Or.inr ⟨rfl, rfl⟩
      · rfl

theorem two_cycle_no_potential : Not (HasPotential TwoCycleEdge) := by
  intro hpot
  rcases hpot with ⟨rho, hdec⟩
  have h01 : rho (1 : Fin 2) < rho (0 : Fin 2) :=
    hdec (0 : Fin 2) (1 : Fin 2) (Or.inl ⟨rfl, rfl⟩)
  have h10 : rho (0 : Fin 2) < rho (1 : Fin 2) :=
    hdec (1 : Fin 2) (0 : Fin 2) (Or.inr ⟨rfl, rfl⟩)
  exact (Nat.lt_irrefl (rho (0 : Fin 2))) (Nat.lt_trans h10 h01)

end RankAudit
end SetStone
