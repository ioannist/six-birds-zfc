namespace SetStone
namespace Packaging

/-!
Mathlib-free structural core for T-ZF-00, Component (iii):
idempotent endomaps split through their fixed-point subtype.
-/

def Idem {A : Type} (e : A -> A) : Prop :=
  forall a, e (e a) = e a

def Fix {A : Type} (e : A -> A) (a : A) : Prop :=
  e a = a

def InImage {A : Type} (e : A -> A) (a : A) : Prop :=
  exists b, e b = a

theorem image_in_fix {A : Type} {e : A -> A} (hidem : Idem e) (a : A) :
    Fix e (e a) := by
  unfold Fix
  exact hidem a

theorem fix_iff_image {A : Type} {e : A -> A} (hidem : Idem e) (a : A) :
    Fix e a <-> InImage e a := by
  constructor
  · intro hfix
    exact ⟨a, hfix⟩
  · intro him
    rcases him with ⟨b, hb⟩
    unfold Fix
    rw [← hb]
    exact hidem b

def retract {A : Type} (e : A -> A) (hidem : Idem e) (a : A) :
    {a : A // Fix e a} :=
  ⟨e a, image_in_fix hidem a⟩

def inclusion {A : Type} {e : A -> A} : {a : A // Fix e a} -> A :=
  Subtype.val

theorem r_i_id {A : Type} {e : A -> A} (hidem : Idem e)
    (x : {a : A // Fix e a}) :
    (retract e hidem (inclusion x)).val = x.val := by
  unfold retract inclusion Fix at *
  exact x.property

theorem i_r_eq_e {A : Type} {e : A -> A} (hidem : Idem e) (a : A) :
    inclusion (retract e hidem a) = e a := by
  rfl

def collapseFin3 : Fin 3 -> Fin 3 :=
  fun k => if k = (2 : Fin 3) then (1 : Fin 3) else k

theorem collapseFin3_zero : collapseFin3 (0 : Fin 3) = (0 : Fin 3) := by
  unfold collapseFin3
  decide

theorem collapseFin3_one : collapseFin3 (1 : Fin 3) = (1 : Fin 3) := by
  unfold collapseFin3
  decide

theorem collapseFin3_two : collapseFin3 (2 : Fin 3) = (1 : Fin 3) := by
  unfold collapseFin3
  decide

theorem collapseFin3_idem : Idem collapseFin3 := by
  intro k
  unfold collapseFin3
  by_cases h : k = (2 : Fin 3)
  · simp [h]
  · simp [h]

theorem collapseFin3_fix_zero : Fix collapseFin3 (0 : Fin 3) := by
  exact collapseFin3_zero

theorem collapseFin3_fix_one : Fix collapseFin3 (1 : Fin 3) := by
  exact collapseFin3_one

theorem collapseFin3_two_not_fixed : Not (Fix collapseFin3 (2 : Fin 3)) := by
  unfold Fix
  rw [collapseFin3_two]
  decide

theorem collapseFin3_fixed_points_distinct :
    (0 : Fin 3) ≠ (1 : Fin 3) := by
  decide

theorem collapseFin3_not_identity :
    exists k, collapseFin3 k ≠ k := by
  exact ⟨(2 : Fin 3), collapseFin3_two_not_fixed⟩

theorem collapseFin3_not_constant :
    exists a b, collapseFin3 a ≠ collapseFin3 b := by
  exact ⟨(0 : Fin 3), (1 : Fin 3), by
    rw [collapseFin3_zero, collapseFin3_one]
    decide⟩

end Packaging
end SetStone
