import Init.Omega

namespace SetStone
namespace HFClosure

/-!
Mathlib-free finite operational core for the T-ZF-01 HF closure step.

`HF` is a presentation type.  `Equiv` is the recursive extensional
equality relation: two presentations are equivalent when every raw
member of either side is matched by an extensionally equivalent raw
member of the other side.  No quotient is taken in this module.
-/

inductive HF where
  | mk : List HF -> HF

def members : HF -> List HF
  | HF.mk xs => xs

/-!
`height` is a presentation-size measure used only to justify recursive
definitions and proofs.  It is not the set-theoretic rank audit.
-/
mutual
  def height : HF -> Nat
    | HF.mk xs => heightList xs

  def heightList : List HF -> Nat
    | [] => 0
    | x :: xs => height x + 1 + heightList xs
end

theorem height_lt_heightList_of_mem (a : HF) :
    forall xs, a ∈ xs -> height a < heightList xs
  | [] => by
      intro h
      cases h
  | _ :: xs => by
      intro h
      cases h with
      | head =>
          unfold heightList
          omega
      | tail _ htail =>
          have ih : height a < heightList xs := height_lt_heightList_of_mem a xs htail
          unfold heightList
          omega

theorem raw_mem_height_lt {a b : HF} (h : a ∈ members b) : height a < height b := by
  cases b with
  | mk xs =>
      exact height_lt_heightList_of_mem a xs h

/-!
The rank audit is the usual finite set rank: one plus the maximum rank
of a raw member, with `0` for empty presentations.  Unlike `height`,
this rank is invariant under recursive extensional equality.
-/
mutual
  def rank : HF -> Nat
    | HF.mk xs => rankList xs

  def rankList : List HF -> Nat
    | [] => 0
    | x :: xs => Nat.max (rank x + 1) (rankList xs)
end

theorem rank_lt_rankList_of_mem (a : HF) :
    forall xs, a ∈ xs -> rank a < rankList xs
  | [] => by
      intro h
      cases h
  | x :: xs => by
      intro h
      cases h with
      | head =>
          unfold rankList
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (rank a))
            (Nat.le_max_left (rank a + 1) (rankList xs))
      | tail _ htail =>
          have ih : rank a < rankList xs := rank_lt_rankList_of_mem a xs htail
          unfold rankList
          exact Nat.lt_of_lt_of_le ih (Nat.le_max_right (rank x + 1) (rankList xs))

theorem raw_mem_rank_lt {a b : HF} (h : a ∈ members b) : rank a < rank b := by
  cases b with
  | mk xs =>
      exact rank_lt_rankList_of_mem a xs h

theorem rankList_le_of_all_lt :
    forall xs n, (forall x, x ∈ xs -> rank x < n) -> rankList xs <= n
  | [], n => by
      intro _
      unfold rankList
      omega
  | x :: xs, n => by
      intro h
      unfold rankList
      have hx : rank x + 1 <= n := by
        have hxlt : rank x < n := h x (List.Mem.head xs)
        omega
      have hxs : rankList xs <= n :=
        rankList_le_of_all_lt xs n (by
          intro y hy
          exact h y (List.Mem.tail x hy))
      exact (Nat.max_le).mpr ⟨hx, hxs⟩

/-!
Recursive extensional equality.  The subtype witnesses make the
membership evidence available to the termination checker.
-/
def Equiv : HF -> HF -> Prop
  | HF.mk xs, HF.mk ys =>
      ((x : HF) -> x ∈ xs -> exists y : {y : HF // y ∈ ys}, Equiv x y.val) /\
      ((y : HF) -> y ∈ ys -> exists x : {x : HF // x ∈ xs}, Equiv y x.val)
termination_by a b => height a + height b
decreasing_by
  simp_wf
  · rename_i hx
    have hxlt : height x < height (HF.mk xs) := raw_mem_height_lt hx
    have hylt : height y.val < height (HF.mk ys) := raw_mem_height_lt y.property
    omega
  · rename_i hy
    have hylt : height y < height (HF.mk ys) := raw_mem_height_lt hy
    have hxlt : height x.val < height (HF.mk xs) := raw_mem_height_lt x.property
    omega

def Mem (a b : HF) : Prop :=
  exists c, c ∈ members b /\ Equiv a c

theorem equiv_refl : (a : HF) -> Equiv a a
  | HF.mk xs => by
      unfold Equiv
      constructor
      · intro x hx
        exact ⟨⟨x, hx⟩, equiv_refl x⟩
      · intro x hx
        exact ⟨⟨x, hx⟩, equiv_refl x⟩
termination_by a => height a
decreasing_by
  all_goals
    simp_wf
    simpa [members] using (raw_mem_height_lt (a := x) (b := HF.mk xs) hx)

theorem equiv_symm {a b : HF} (h : Equiv a b) : Equiv b a := by
  cases a with
  | mk xs =>
      cases b with
      | mk ys =>
          unfold Equiv at h ⊢
          exact ⟨h.2, h.1⟩

theorem equiv_trans : (a b c : HF) -> Equiv a b -> Equiv b c -> Equiv a c
  | HF.mk xs, HF.mk ys, HF.mk zs, hab, hbc => by
      unfold Equiv at hab hbc ⊢
      constructor
      · intro x hx
        rcases hab.1 x hx with ⟨y, hxy⟩
        rcases hbc.1 y.val y.property with ⟨z, hyz⟩
        exact ⟨z, equiv_trans x y.val z.val hxy hyz⟩
      · intro z hz
        rcases hbc.2 z hz with ⟨y, hzy⟩
        rcases hab.2 y.val y.property with ⟨x, hyx⟩
        exact ⟨x, equiv_trans z y.val x.val hzy hyx⟩
termination_by a b c => height a + height b + height c
decreasing_by
  simp_wf
  · have hxlt : height x < height (HF.mk xs) := raw_mem_height_lt hx
    have hylt : height y.val < height (HF.mk ys) := raw_mem_height_lt y.property
    have hzlt : height z.val < height (HF.mk zs) := raw_mem_height_lt z.property
    omega
  · have hzlt : height z < height (HF.mk zs) := raw_mem_height_lt hz
    have hylt : height y.val < height (HF.mk ys) := raw_mem_height_lt y.property
    have hxlt : height x.val < height (HF.mk xs) := raw_mem_height_lt x.property
    omega

theorem rank_le_of_equiv : (a b : HF) -> Equiv a b -> rank a <= rank b
  | HF.mk xs, HF.mk ys, h => by
      unfold Equiv at h
      unfold rank
      apply rankList_le_of_all_lt
      intro x hx
      rcases h.1 x hx with ⟨y, hxy⟩
      have hle : rank x <= rank y.val := rank_le_of_equiv x y.val hxy
      have hylt : rank y.val < rank (HF.mk ys) := raw_mem_rank_lt y.property
      exact Nat.lt_of_le_of_lt hle hylt
termination_by a b => height a + height b
decreasing_by
  simp_wf
  have hxlt : height x < height (HF.mk xs) := raw_mem_height_lt hx
  have hylt : height y.val < height (HF.mk ys) := raw_mem_height_lt y.property
  omega

theorem rank_eq_of_equiv {a b : HF} (h : Equiv a b) : rank a = rank b := by
  exact Nat.le_antisymm (rank_le_of_equiv a b h) (rank_le_of_equiv b a (equiv_symm h))

theorem mem_congr_right {a b c : HF} (hbc : Equiv b c) : Mem a b <-> Mem a c := by
  constructor
  · intro h
    rcases h with ⟨x, hxb, hax⟩
    cases b with
    | mk xs =>
        cases c with
        | mk ys =>
            unfold Equiv at hbc
            rcases hbc.1 x hxb with ⟨y, hxy⟩
            exact ⟨y.val, y.property, equiv_trans a x y.val hax hxy⟩
  · intro h
    rcases h with ⟨x, hxc, hax⟩
    cases b with
    | mk xs =>
        cases c with
        | mk ys =>
            unfold Equiv at hbc
            rcases hbc.2 x hxc with ⟨y, hxy⟩
            exact ⟨y.val, y.property, equiv_trans a x y.val hax hxy⟩

def emptyHF : HF :=
  HF.mk []

theorem not_mem_emptyHF (a : HF) : Not (Mem a emptyHF) := by
  intro h
  rcases h with ⟨c, hc, _⟩
  cases hc

def pairHF (a b : HF) : HF :=
  HF.mk [a, b]

theorem mem_pairHF_iff (a b c : HF) :
    Mem c (pairHF a b) <-> (Equiv c a \/ Equiv c b) := by
  constructor
  · intro h
    rcases h with ⟨d, hd, hcd⟩
    cases hd with
    | head =>
        exact Or.inl hcd
    | tail _ hd2 =>
        cases hd2 with
        | head =>
            exact Or.inr hcd
        | tail _ hdNil =>
            cases hdNil
  · intro h
    cases h with
    | inl hca =>
        exact ⟨a, List.Mem.head _, hca⟩
    | inr hcb =>
        exact ⟨b, List.Mem.tail _ (List.Mem.head _), hcb⟩

def flattenMembers : List HF -> List HF
  | [] => []
  | x :: xs => members x ++ flattenMembers xs

theorem mem_flattenMembers_iff (c : HF) :
    forall xs, c ∈ flattenMembers xs <-> exists d, d ∈ xs /\ c ∈ members d
  | [] => by
      constructor
      · intro h
        cases h
      · intro h
        rcases h with ⟨d, hd, _⟩
        cases hd
  | x :: xs => by
      constructor
      · intro h
        unfold flattenMembers at h
        have hmem : c ∈ members x \/ c ∈ flattenMembers xs := List.mem_append.mp h
        cases hmem with
        | inl hx =>
            exact ⟨x, List.Mem.head _, hx⟩
        | inr hxs =>
            have ih := (mem_flattenMembers_iff c xs).mp hxs
            rcases ih with ⟨d, hd, hcd⟩
            exact ⟨d, List.Mem.tail _ hd, hcd⟩
      · intro h
        rcases h with ⟨d, hd, hcd⟩
        unfold flattenMembers
        cases hd with
        | head =>
            exact List.mem_append.mpr (Or.inl hcd)
        | tail _ hdTail =>
            have hflat : c ∈ flattenMembers xs :=
              (mem_flattenMembers_iff c xs).mpr ⟨d, hdTail, hcd⟩
            exact List.mem_append.mpr (Or.inr hflat)

def unionHF (a : HF) : HF :=
  HF.mk (flattenMembers (members a))

theorem mem_unionHF_iff (a c : HF) :
    Mem c (unionHF a) <-> exists d, Mem d a /\ Mem c d := by
  constructor
  · intro h
    rcases h with ⟨e, he, hce⟩
    have hflat := (mem_flattenMembers_iff e (members a)).mp he
    rcases hflat with ⟨d, hda, hed⟩
    exact ⟨d, ⟨d, hda, equiv_refl d⟩, ⟨e, hed, hce⟩⟩
  · intro h
    rcases h with ⟨d, hda, hcd⟩
    rcases hda with ⟨d0, hd0a, hdd0⟩
    rcases hcd with ⟨e, hed, hce⟩
    cases d with
    | mk dmembers =>
        cases d0 with
        | mk d0members =>
            unfold Equiv at hdd0
            rcases hdd0.1 e hed with ⟨e0, hee0⟩
            have hflat : e0.val ∈ flattenMembers (members a) :=
              (mem_flattenMembers_iff e0.val (members a)).mpr ⟨HF.mk d0members, hd0a, e0.property⟩
            exact ⟨e0.val, hflat, equiv_trans c e e0.val hce hee0⟩

def collect : List HF -> HF
  | [] => emptyHF
  | y :: ys => unionHF (pairHF (collect ys) (pairHF y y))

theorem mem_collect_iff (xs : List HF) (c : HF) :
    Mem c (collect xs) <-> exists d, d ∈ xs /\ Equiv c d := by
  induction xs with
  | nil =>
      constructor
      · intro h
        exact False.elim (not_mem_emptyHF c h)
      · intro h
        rcases h with ⟨d, hd, _⟩
        cases hd
  | cons y ys ih =>
      constructor
      · intro h
        have hu := (mem_unionHF_iff (pairHF (collect ys) (pairHF y y)) c).mp h
        rcases hu with ⟨d, hdPair, hcd⟩
        have hpair := (mem_pairHF_iff (collect ys) (pairHF y y) d).mp hdPair
        cases hpair with
        | inl hdCollect =>
            have hcCollect : Mem c (collect ys) := (mem_congr_right hdCollect).mp hcd
            rcases ih.mp hcCollect with ⟨e, heys, hce⟩
            exact ⟨e, List.Mem.tail y heys, hce⟩
        | inr hdSingleton =>
            have hcSingleton : Mem c (pairHF y y) := (mem_congr_right hdSingleton).mp hcd
            have hcy := (mem_pairHF_iff y y c).mp hcSingleton
            cases hcy with
            | inl hcy1 =>
                exact ⟨y, List.Mem.head ys, hcy1⟩
            | inr hcy2 =>
                exact ⟨y, List.Mem.head ys, hcy2⟩
      · intro h
        rcases h with ⟨d, hd, hcd⟩
        have hUnion : exists e, Mem e (pairHF (collect ys) (pairHF y y)) /\ Mem c e := by
          cases hd with
          | head =>
              exact ⟨pairHF y y,
                (mem_pairHF_iff (collect ys) (pairHF y y) (pairHF y y)).mpr
                  (Or.inr (equiv_refl (pairHF y y))),
                (mem_pairHF_iff y y c).mpr (Or.inl hcd)⟩
          | tail _ hdys =>
              have hcCollect : Mem c (collect ys) := ih.mpr ⟨d, hdys, hcd⟩
              exact ⟨collect ys,
                (mem_pairHF_iff (collect ys) (pairHF y y) (collect ys)).mpr
                  (Or.inl (equiv_refl (collect ys))),
                hcCollect⟩
        exact (mem_unionHF_iff (pairHF (collect ys) (pairHF y y)) c).mpr hUnion

theorem mem_rank_lt {a b : HF} (h : Mem a b) : rank a < rank b := by
  rcases h with ⟨c, hcb, hac⟩
  have hca : rank a = rank c := rank_eq_of_equiv hac
  have hcbRank : rank c < rank b := raw_mem_rank_lt hcb
  rw [hca]
  exact hcbRank

/-! Semantic bridges: presentation equality is not set equality. -/

theorem mem_congr_left {a b c : HF} (hab : Equiv a b) : Mem a c <-> Mem b c := by
  constructor
  · rintro ⟨d, hd, had⟩
    exact ⟨d, hd, equiv_trans b a d (equiv_symm hab) had⟩
  · rintro ⟨d, hd, hbd⟩
    exact ⟨d, hd, equiv_trans a b d hab hbd⟩

theorem equiv_iff_mem (a b : HF) :
    Equiv a b <-> (forall c, Mem c a <-> Mem c b) := by
  constructor
  · intro h c
    exact mem_congr_right h
  · intro h
    cases a with
    | mk xs =>
      cases b with
      | mk ys =>
        unfold Equiv
        constructor
        · intro x hx
          rcases (h x).mp ⟨x, hx, equiv_refl x⟩ with ⟨y, hy, hxy⟩
          exact ⟨⟨y, hy⟩, hxy⟩
        · intro y hy
          rcases (h y).mpr ⟨y, hy, equiv_refl y⟩ with ⟨x, hx, hyx⟩
          exact ⟨⟨x, hx⟩, hyx⟩

theorem pairHF_congr {a a' b b' : HF} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (pairHF a b) (pairHF a' b') := by
  apply (equiv_iff_mem _ _).mpr
  intro c
  rw [mem_pairHF_iff, mem_pairHF_iff]
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inl (equiv_trans c a a' h ha)
    | inr h => exact Or.inr (equiv_trans c b b' h hb)
  · intro h
    cases h with
    | inl h => exact Or.inl (equiv_trans c a' a h (equiv_symm ha))
    | inr h => exact Or.inr (equiv_trans c b' b h (equiv_symm hb))

theorem unionHF_congr {a b : HF} (h : Equiv a b) : Equiv (unionHF a) (unionHF b) := by
  apply (equiv_iff_mem _ _).mpr
  intro c
  rw [mem_unionHF_iff, mem_unionHF_iff]
  constructor
  · rintro ⟨d, hd, hc⟩
    exact ⟨d, (mem_congr_right h).mp hd, hc⟩
  · rintro ⟨d, hd, hc⟩
    exact ⟨d, (mem_congr_right h).mpr hd, hc⟩

theorem collect_equiv_mk (xs : List HF) : Equiv (collect xs) (HF.mk xs) := by
  apply (equiv_iff_mem _ _).mpr
  intro c
  exact mem_collect_iff xs c

def filterHF (p : HF -> Bool) (a : HF) : HF := HF.mk ((members a).filter p)

theorem mem_filterHF_iff (p : HF -> Bool)
    (hp : forall {a b}, Equiv a b -> p a = p b) (a c : HF) :
    Mem c (filterHF p a) <-> (Mem c a /\ p c = true) := by
  constructor
  · rintro ⟨d, hd, hcd⟩
    have hd' : d ∈ members a /\ p d = true := List.mem_filter.mp hd
    exact ⟨⟨d, hd'.1, hcd⟩, (hp hcd).trans hd'.2⟩
  · rintro ⟨⟨d, hd, hcd⟩, hc⟩
    exact ⟨d, List.mem_filter.mpr ⟨hd, (hp hcd).symm.trans hc⟩, hcd⟩

theorem filterHF_congr (p : HF -> Bool)
    (hp : forall {a b}, Equiv a b -> p a = p b)
    {a b : HF} (hab : Equiv a b) : Equiv (filterHF p a) (filterHF p b) := by
  apply (equiv_iff_mem _ _).mpr
  intro c
  rw [mem_filterHF_iff p hp, mem_filterHF_iff p hp]
  constructor
  · intro h
    exact ⟨(mem_congr_right hab).mp h.1, h.2⟩
  · intro h
    exact ⟨(mem_congr_right hab).mpr h.1, h.2⟩

/-! Empty, pairing and union already generate every extensional HF object.
The family must respect `Equiv`; arbitrary raw presentation equality would
retain ordering and duplicates and would be the wrong target. -/
structure ClosedFamily (A : HF -> Prop) : Prop where
  respects : forall {a b}, Equiv a b -> A a -> A b
  empty : A emptyHF
  pair : forall {a b}, A a -> A b -> A (pairHF a b)
  union : forall {a}, A a -> A (unionHF a)

theorem collect_in_closed {A : HF -> Prop} (hA : ClosedFamily A) :
    forall xs, (forall x, x ∈ xs -> A x) -> A (collect xs)
  | [], _ => hA.empty
  | y :: ys, h => by
    exact hA.union (hA.pair
      (collect_in_closed hA ys (fun x hx => h x (List.Mem.tail y hx)))
      (hA.pair (h y (List.Mem.head ys)) (h y (List.Mem.head ys))))

theorem closed_contains_all {A : HF -> Prop} (hA : ClosedFamily A) : forall a, A a
  | HF.mk xs => by
    apply hA.respects (collect_equiv_mk xs)
    apply collect_in_closed hA
    intro x hx
    exact closed_contains_all hA x
termination_by a => height a
decreasing_by
  simp_wf
  exact height_lt_heightList_of_mem x xs hx

def singletonHF (a : HF) : HF := pairHF a a
def succHF (a : HF) : HF := unionHF (pairHF a (singletonHF a))

theorem mem_self_succHF (a : HF) : Mem a (succHF a) := by
  apply (mem_unionHF_iff _ _).mpr
  exact ⟨singletonHF a,
    (mem_pairHF_iff _ _ _).mpr (Or.inr (equiv_refl _)),
    (mem_pairHF_iff _ _ _).mpr (Or.inl (equiv_refl _))⟩

theorem rank_succHF_gt (a : HF) : rank a < rank (succHF a) :=
  mem_rank_lt (mem_self_succHF a)

/-! No inductive object exists. The proof uses the member with maximal rank
in a finite presentation, rather than assuming an infinite family of ordinals. -/
theorem rankList_attained : forall xs, xs ≠ [] ->
    exists x, x ∈ xs /\ rankList xs = rank x + 1
  | [], h => False.elim (h rfl)
  | x :: xs, _ => by
    cases xs with
    | nil => exact ⟨x, List.Mem.head [], by simp [rankList]⟩
    | cons y ys =>
      rcases rankList_attained (y :: ys) (by intro h; cases h) with ⟨m, hm, hr⟩
      by_cases h : rank x + 1 <= rankList (y :: ys)
      · exact ⟨m, List.Mem.tail x hm, by
          change Nat.max (rank x + 1) (rankList (y :: ys)) = _
          simp only [Nat.max_def]
          split <;> omega⟩
      · exact ⟨x, List.Mem.head _, by
          change Nat.max (rank x + 1) (rankList (y :: ys)) = _
          simp only [Nat.max_def]
          split <;> omega⟩

def InductiveHF (a : HF) : Prop :=
  Mem emptyHF a /\ forall x, Mem x a -> Mem (succHF x) a

theorem not_inductiveHF (a : HF) : Not (InductiveHF a) := by
  intro h
  cases a with
  | mk xs =>
    have hne : xs ≠ [] := by
      intro he
      subst xs
      exact not_mem_emptyHF emptyHF h.1
    rcases rankList_attained xs hne with ⟨x, hx, hr⟩
    have hs := mem_rank_lt (h.2 x ⟨x, hx, equiv_refl x⟩)
    have hxlt := rank_succHF_gt x
    change rank (succHF x) < rankList xs at hs
    omega

end HFClosure
end SetStone
