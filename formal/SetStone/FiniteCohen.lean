namespace SetStone
namespace FiniteCohen

def Predicate (N : Nat) := Fin N -> Bool

def Condition (N : Nat) := Fin N -> Option Bool

def Extends {N : Nat} (q p : Condition N) : Prop :=
  forall z b, p z = some b -> q z = some b

def InG {N : Nat} (h : Predicate N) (p : Condition N) : Prop :=
  forall z b, p z = some b -> h z = b

def D {N : Nat} (g : Predicate N) (p : Condition N) : Prop :=
  exists z, exists b, p z = some b /\ b ≠ g z

def E {N K : Nat} (f : Fin N -> Fin K) (x : Fin K) (p : Condition N) : Prop :=
  exists z, exists z',
    f z = x /\ f z' = x /\
    exists b, exists b', p z = some b /\ p z' = some b' /\ b ≠ b'

def Splits {N K : Nat} (f : Fin N -> Fin K) (x : Fin K) (h : Predicate N) : Prop :=
  exists z, exists z', f z = x /\ f z' = x /\ h z ≠ h z'

def Total {N : Nat} (g : Predicate N) : Condition N :=
  fun z => some (g z)

def F_D {N : Nat} (g : Predicate N) (p : Condition N) : Prop :=
  Not (exists q, Extends q p /\ D g q)

def F_E {N K : Nat} (f : Fin N -> Fin K) (x : Fin K) (p : Condition N) : Prop :=
  Not (exists q, Extends q p /\ E f x q)

def BlockConstant {N K : Nat} (f : Fin N -> Fin K) (x : Fin K)
    (p : Condition N) : Prop :=
  exists c : Bool, forall z, f z = x -> p z = some c

def HasTwo {N K : Nat} (f : Fin N -> Fin K) (x : Fin K) : Prop :=
  exists z, exists z', f z = x /\ f z' = x /\ z ≠ z'

def emptyCondition {N : Nat} : Condition N :=
  fun _ => none

def setAt {N : Nat} (p : Condition N) (z : Fin N) (b : Bool) : Condition N :=
  fun w => if w = z then some b else p w

def twoAt {N : Nat} (z z2 : Fin N) (b b2 : Bool) : Condition N :=
  fun w => setAt (setAt emptyCondition z b) z2 b2 w

theorem bool_not_ne (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

theorem some_bool_inj {a b : Bool} (h : some a = some b) : a = b := by
  cases h
  rfl

theorem extends_refl {N : Nat} (p : Condition N) : Extends p p := by
  intro z b hp
  exact hp

theorem extends_trans {N : Nat} {r q p : Condition N}
    (hrq : Extends r q) (hqp : Extends q p) : Extends r p := by
  intro z b hp
  exact hrq z b (hqp z b hp)

theorem setAt_self {N : Nat} (p : Condition N) (z : Fin N) (b : Bool) :
    setAt p z b z = some b := by
  unfold setAt
  simp

theorem setAt_of_ne {N : Nat} (p : Condition N) {z w : Fin N} (b : Bool)
    (h : w ≠ z) : setAt p z b w = p w := by
  unfold setAt
  simp [h]

theorem setAt_extends_of_none {N : Nat} {p : Condition N} {z : Fin N} {b : Bool}
    (hz : p z = none) : Extends (setAt p z b) p := by
  intro w c hw
  unfold setAt
  by_cases h : w = z
  · subst w
    rw [hz] at hw
    contradiction
  · simp [h, hw]

theorem setAt_was_none_of_ne {N : Nat} {p : Condition N} {z w : Fin N} {b : Bool}
    (hw : p w = none) (hne : w ≠ z) : setAt p z b w = none := by
  rw [setAt_of_ne p b hne, hw]

theorem twoAt_left {N : Nat} {z z' : Fin N} {b b' : Bool} (hne : z ≠ z') :
    twoAt z z' b b' z = some b := by
  unfold twoAt
  rw [setAt_of_ne (setAt emptyCondition z b) b' hne]
  exact setAt_self emptyCondition z b

theorem twoAt_right {N : Nat} {z z' : Fin N} {b b' : Bool} :
    twoAt z z' b b' z' = some b' := by
  unfold twoAt
  exact setAt_self (setAt emptyCondition z b) z' b'

theorem twoAt_InG {N : Nat} {h : Predicate N} {z z' : Fin N} :
    InG h (twoAt z z' (h z) (h z')) := by
  intro w b hw
  unfold twoAt at hw
  by_cases hwz' : w = z'
  · subst w
    rw [setAt_self] at hw
    exact some_bool_inj hw
  · rw [setAt_of_ne (setAt emptyCondition z (h z)) (h z') hwz'] at hw
    by_cases hwz : w = z
    · subst w
      rw [setAt_self] at hw
      exact some_bool_inj hw
    · rw [setAt_of_ne emptyCondition (h z) hwz] at hw
      unfold emptyCondition at hw
      contradiction

theorem oneAt_InG {N : Nat} {h : Predicate N} {z : Fin N} :
    InG h (setAt emptyCondition z (h z)) := by
  intro w b hw
  by_cases hwz : w = z
  · subst w
    rw [setAt_self] at hw
    exact some_bool_inj hw
  · rw [setAt_of_ne emptyCondition (h z) hwz] at hw
    unfold emptyCondition at hw
    contradiction

theorem pointwise_eq_of_not_exists_ne {N : Nat} {h g : Predicate N}
    (hn : Not (exists z, h z ≠ g z)) : h = g := by
  funext z
  cases hz : h z <;> cases gz : g z
  · rfl
  · exfalso
    exact hn ⟨z, by rw [hz, gz]; decide⟩
  · exfalso
    exact hn ⟨z, by rw [hz, gz]; decide⟩
  · rfl

theorem meet_D_iff_neq {N : Nat} (h g : Predicate N) :
    (exists p, InG h p /\ D g p) <-> h ≠ g := by
  constructor
  · intro hex heq
    rcases hex with ⟨p, hG, z, b, hp, hne⟩
    have hb : h z = b := hG z b hp
    have hzg : h z = g z := congrArg (fun u => u z) heq
    exact hne (hb.symm.trans hzg)
  · intro hneq
    have hpoint : exists z, h z ≠ g z := by
      by_cases hex : exists z, h z ≠ g z
      · exact hex
      · exact False.elim (hneq (pointwise_eq_of_not_exists_ne hex))
    rcases hpoint with ⟨z, hz⟩
    let p : Condition N := setAt emptyCondition z (h z)
    refine Exists.intro p ?_
    constructor
    · exact oneAt_InG
    · refine Exists.intro z ?_
      refine Exists.intro (h z) ?_
      constructor
      · exact setAt_self emptyCondition z (h z)
      · exact hz

theorem meet_E_iff_splits {N K : Nat} (f : Fin N -> Fin K) (x : Fin K)
    (h : Predicate N) :
    (exists p, InG h p /\ E f x p) <-> Splits f x h := by
  constructor
  · intro hex
    rcases hex with ⟨p, hG, z, z', hfz, hfz', b, b', hpz, hpz', hne⟩
    refine ⟨z, z', hfz, hfz', ?_⟩
    intro hh
    have hb : h z = b := hG z b hpz
    have hb' : h z' = b' := hG z' b' hpz'
    have : b = b' := hb.symm.trans (hh.trans hb')
    exact hne this
  · intro hs
    rcases hs with ⟨z, z', hfz, hfz', hneq⟩
    have zne : z' ≠ z := by
      intro hzz
      apply hneq
      rw [hzz]
    let p : Condition N := twoAt z z' (h z) (h z')
    refine ⟨p, ?_, ?_⟩
    · exact twoAt_InG
    · refine ⟨z, z', hfz, hfz', h z, h z', ?_, ?_, hneq⟩
      · apply twoAt_left
        intro hzz'
        exact zne hzz'.symm
      · exact twoAt_right

theorem D_of_disagrees {N : Nat} {g : Predicate N} {p : Condition N}
    {z : Fin N} {b : Bool} (hp : p z = some b) (hne : b ≠ g z) : D g p := by
  exact ⟨z, b, hp, hne⟩

theorem not_F_D_of_D {N : Nat} {g : Predicate N} {p : Condition N}
    (hd : D g p) : Not (F_D g p) := by
  intro hf
  exact hf ⟨p, extends_refl p, hd⟩

theorem density_D_failure_iff_total {N : Nat} (g : Predicate N) (p : Condition N) :
    F_D g p <-> (forall z, p z = some (g z)) := by
  constructor
  · intro hf z
    cases hp : p z with
    | none =>
        let q : Condition N := setAt p z (!g z)
        have hExt : Extends q p := setAt_extends_of_none hp
        have hqz : q z = some (!g z) := setAt_self p z (!g z)
        have hd : D g q := D_of_disagrees hqz (bool_not_ne (g z))
        exact False.elim (hf ⟨q, hExt, hd⟩)
    | some b =>
        by_cases hb : b = g z
        · rw [hb]
        · have hd : D g p := D_of_disagrees hp hb
          exact False.elim ((not_F_D_of_D hd) hf)
  · intro htotal hbad
    rcases hbad with ⟨q, hExt, z, b, hqz, hne⟩
    have hqz' : q z = some (g z) := hExt z (g z) (htotal z)
    have hb : b = g z := some_bool_inj (hqz.symm.trans hqz')
    exact hne hb

theorem not_E_self_of_F_E {N K : Nat} {f : Fin N -> Fin K} {x : Fin K}
    {p : Condition N} (hf : F_E f x p) : Not (E f x p) := by
  intro he
  exact hf ⟨p, extends_refl p, he⟩

theorem no_split_assigned_values {N K : Nat} {f : Fin N -> Fin K} {x : Fin K}
    {p : Condition N} (hf : F_E f x p)
    {z z' : Fin N} (hfz : f z = x) (hfz' : f z' = x)
    {b b' : Bool} (hpz : p z = some b) (hpz' : p z' = some b') : b = b' := by
  by_cases hbb : b = b'
  · exact hbb
  · have he : E f x p := ⟨z, z', hfz, hfz', b, b', hpz, hpz', hbb⟩
    exact False.elim ((not_E_self_of_F_E hf) he)

theorem other_in_two {N K : Nat} {f : Fin N -> Fin K} {x : Fin K}
    (htwo : HasTwo f x) (z : Fin N) :
    exists w, f w = x /\ w ≠ z := by
  rcases htwo with ⟨a, b, hfa, hfb, hne⟩
  by_cases hz : z = a
  · exact ⟨b, hfb, by
      intro hbz
      have hba : b = a := hbz.trans hz
      exact hne hba.symm⟩
  · exact ⟨a, hfa, by
      intro haz
      exact hz haz.symm⟩

theorem assigns_block_of_F_E {N K : Nat} {f : Fin N -> Fin K} {x : Fin K}
    {p : Condition N} (htwo : HasTwo f x) (hf : F_E f x p)
    {z : Fin N} (hfz : f z = x) : exists b, p z = some b := by
  cases hpz : p z with
  | some b =>
      exact ⟨b, rfl⟩
  | none =>
      rcases other_in_two htwo z with ⟨w, hfw, hwnez⟩
      cases hpw : p w with
      | some bw =>
          let q : Condition N := setAt p z (!bw)
          have hExt : Extends q p := setAt_extends_of_none hpz
          have hqz : q z = some (!bw) := setAt_self p z (!bw)
          have hqw : q w = some bw := by
            change setAt p z (!bw) w = some bw
            rw [setAt_of_ne p (!bw) hwnez, hpw]
          have he : E f x q :=
            ⟨z, w, hfz, hfw, !bw, bw, hqz, hqw, bool_not_ne bw⟩
          exact False.elim (hf ⟨q, hExt, he⟩)
      | none =>
          let q1 : Condition N := setAt p z false
          let q : Condition N := setAt q1 w true
          have hq1Ext : Extends q1 p := setAt_extends_of_none hpz
          have hq1wNone : q1 w = none := by
            change setAt p z false w = none
            rw [setAt_of_ne p false hwnez, hpw]
          have hqExtq1 : Extends q q1 := setAt_extends_of_none hq1wNone
          have hExt : Extends q p := extends_trans hqExtq1 hq1Ext
          have hqz : q z = some false := by
            have hzw : z ≠ w := by
              intro h
              exact hwnez h.symm
            change setAt q1 w true z = some false
            rw [setAt_of_ne q1 true hzw]
            change setAt p z false z = some false
            exact setAt_self p z false
          have hqw : q w = some true := setAt_self q1 w true
          have he : E f x q :=
            ⟨z, w, hfz, hfw, false, true, hqz, hqw, by decide⟩
          exact False.elim (hf ⟨q, hExt, he⟩)

theorem density_E_failure_iff_constant {N K : Nat} (f : Fin N -> Fin K)
    (x : Fin K) (htwo : HasTwo f x) (p : Condition N) :
    F_E f x p <-> BlockConstant f x p := by
  constructor
  · intro hf
    rcases htwo with ⟨a, a', hfa, hfa', hane⟩
    have htwo' : HasTwo f x := ⟨a, a', hfa, hfa', hane⟩
    rcases assigns_block_of_F_E htwo' hf hfa with ⟨c, hpa⟩
    refine ⟨c, ?_⟩
    intro z hfz
    rcases assigns_block_of_F_E htwo' hf hfz with ⟨b, hpz⟩
    have hb : b = c := no_split_assigned_values hf hfz hfa hpz hpa
    rw [hpz, hb]
  · intro hconst hbad
    rcases hconst with ⟨c, hc⟩
    rcases hbad with ⟨q, hExt, z, z', hfz, hfz', b, b', hqz, hqz', hne⟩
    have hqzc : q z = some c := hExt z c (hc z hfz)
    have hqz'c : q z' = some c := hExt z' c (hc z' hfz')
    have hb : b = c := some_bool_inj (hqz.symm.trans hqzc)
    have hb' : b' = c := some_bool_inj (hqz'.symm.trans hqz'c)
    exact hne (hb.trans hb'.symm)

/-! Actual dense sets in the finite poset. Every total predicate meets every
such set, since total conditions are maximal. Disagreement families D_g are
NOT dense in this poset; their counting interpretation is a defect statistic,
not a characterization of genericity for the finite forcing order. -/
def Dense {N : Nat} (A : Condition N -> Prop) : Prop :=
  forall p, exists q, Extends q p /\ A q

theorem extends_total_eq {N : Nat} {h : Predicate N} {q : Condition N}
    (he : Extends q (Total h)) : q = Total h := by
  funext z
  exact he z (h z) rfl

theorem every_total_meets_dense {N : Nat} (h : Predicate N)
    (A : Condition N -> Prop) (hd : Dense A) : exists p, InG h p /\ A p := by
  rcases hd (Total h) with ⟨q, he, hq⟩
  have hqt := extends_total_eq he
  subst q
  refine ⟨Total h, ?_, hq⟩
  intro z b hz
  exact some_bool_inj hz

theorem disagreement_not_dense {N : Nat} (g : Predicate N) : Not (Dense (D g)) := by
  intro hd
  have hf : F_D g (Total g) := (density_D_failure_iff_total g (Total g)).mpr (fun _ => rfl)
  exact hf (hd (Total g))

end FiniteCohen
end SetStone
