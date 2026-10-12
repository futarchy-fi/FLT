/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineHomogeneousCoordinates
public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.ProjectiveLineTranslationLinear

/-!
# Homogeneous reversal and the original glued endpoint reversal

Exchanging the two homogeneous forms gives the actual endpoint reversal
on the glued projective line, including both whole affine charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
namespace FLT.Mazur.ProjectiveLine
open ProjectiveSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (R : Type u) [CommRing R]

/-- Exchange the two homogeneous coordinate forms. -/
def reversalMap : (ULift.{u} (Fin 2) →₀ R) →ₗ[R] (ULift.{u} (Fin 2) →₀ R) :=
  Finsupp.linearCombination R (fun i =>
    ![Finsupp.single (ULift.up 1) 1, Finsupp.single (ULift.up 0) 1] i.down)

/-- Exchange is involutive on the full module of forms. -/
theorem reversalMap_involutive :
    (reversalMap R).comp (reversalMap R) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i r
  rcases i with ⟨i⟩
  fin_cases i <;> ext ⟨j⟩ <;> fin_cases j <;>
    simp [reversalMap, Finsupp.linearCombination_single]

/-- The involutive linear equivalence giving reciprocal projective coordinates. -/
def reversalLinear : (ULift.{u} (Fin 2) →₀ R) ≃ₗ[R] (ULift.{u} (Fin 2) →₀ R) :=
  LinearEquiv.ofLinearMap (reversalMap R) (reversalMap R)
    (reversalMap_involutive R) (reversalMap_involutive R)

/-- The homogeneous endpoint reversal over arbitrary coefficient rings. -/
def reversalProjIso : space R (ULift.{u} (Fin 2)) ≅ space R (ULift.{u} (Fin 2)) :=
  linearIso (reversalLinear R)

/-- The substitution exchanges the two variables exactly. -/
theorem reversal_substitution (i : ULift.{u} (Fin 2)) :
    linearSubstitution (reversalMap R) (X i) =
      ![X (ULift.up 1), X (ULift.up 0)] i.down := by
  rcases i with ⟨i⟩
  fin_cases i <;> simp [linearSubstitution_X, reversalMap, Finsupp.linearCombination_single]

/-- Reversal has the full homogeneous formula over any test algebra. -/
@[reassoc] theorem reversalProjIso_point {T : Type u} [CommRing T]
    (f : R →+* T) (x : ULift.{u} (Fin 2) → T)
    (i j : ULift.{u} (Fin 2)) (b c : Tˣ) (hi : x i = b)
    (hj : (![x (ULift.up 1), x (ULift.up 0)] : Fin 2 → T) j.down = c) :
    unitChartPoint R (ULift.{u} (Fin 2)) f x i b hi ≫ (reversalProjIso R).hom =
      unitChartPoint R (ULift.{u} (Fin 2)) f
        (fun k => ![x (ULift.up 1), x (ULift.up 0)] k.down) j c hj := by
  apply unitChartPoint_linearIso_of_eval
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [linearGradedMap, linearSubstitution]
  · intro k
    change eval₂Hom f x (linearSubstitution (reversalMap R) (X k)) = _
    rw [reversal_substitution]
    rcases k with ⟨k⟩
    fin_cases k <;> simp

variable (K : Type u) [Field K]

/-- Homogeneous reversal is the original glued endpoint reversal on the whole scheme. -/
@[reassoc] theorem homogeneousIso_reversal :
    (homogeneousIso K).hom ≫ (reversalProjIso K).hom =
      endpointReversal K ≫ (homogeneousIso K).hom := by
  apply (cancel_mono (homogeneousIso K).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    have h := reversalProjIso_point K (Polynomial.C : K →+* Polynomial K)
      (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial K) i.down)
      (ULift.up 0) (ULift.up 1) 1 1 rfl rfl
    have hl := homogeneousPoint_left K (Polynomial.C : K →+* Polynomial K)
      (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial K) i.down) 1 rfl
    have hr := homogeneousPoint_right K (Polynomial.C : K →+* Polynomial K)
      (fun i => (![Polynomial.X, 1] : Fin 2 → Polynomial K) i.down) 1 rfl
    have he : Polynomial.eval₂RingHom (Polynomial.C : K →+* Polynomial K) Polynomial.X =
        RingHom.id _ := by ext <;> simp
    simp only [inv_one, Units.val_one, one_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, he, CommRingCat.ofHom_id,
      Spec.map_id, Category.id_comp] at hl hr
    rw [left_endpointReversal K, ← hl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, h]
    exact hr
  · change right K ≫ _ = right K ≫ _
    have h := reversalProjIso_point K (Polynomial.C : K →+* Polynomial K)
      (fun i => (![Polynomial.X, 1] : Fin 2 → Polynomial K) i.down)
      (ULift.up 1) (ULift.up 0) 1 1 rfl rfl
    have hr := homogeneousPoint_right K (Polynomial.C : K →+* Polynomial K)
      (fun i => (![Polynomial.X, 1] : Fin 2 → Polynomial K) i.down) 1 rfl
    have hl := homogeneousPoint_left K (Polynomial.C : K →+* Polynomial K)
      (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial K) i.down) 1 rfl
    have he : Polynomial.eval₂RingHom (Polynomial.C : K →+* Polynomial K) Polynomial.X =
        RingHom.id _ := by ext <;> simp
    simp only [inv_one, Units.val_one, one_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, he, CommRingCat.ofHom_id,
      Spec.map_id, Category.id_comp] at hl hr
    rw [right_endpointReversal K, ← hr]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, h]
    exact hl

end FLT.Mazur.ProjectiveLine
