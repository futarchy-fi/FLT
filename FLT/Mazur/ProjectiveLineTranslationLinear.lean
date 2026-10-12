/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineSlopeNormalizationLinear
public import FLT.Mazur.ProjectiveLinearCoefficientChange

/-!
# Translation on complete homogeneous lines

The substitution [x₀:x₁] ↦ [x₀:x₁+a*x₀] extends affine translation
across infinity over any ring, without an invertibility assumption on a.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FLT.Mazur.ProjectiveLine
open ProjectiveSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (a : R)

/-- Homogeneous coordinate forms for translation by a. -/
def translationMap : (ULift.{u} (Fin 2) →₀ R) →ₗ[R] (ULift.{u} (Fin 2) →₀ R) :=
  Finsupp.linearCombination R (fun i =>
    ![Finsupp.single (ULift.up 0) 1,
      Finsupp.single (ULift.up 1) 1 + a • Finsupp.single (ULift.up 0) 1] i.down)

/-- Opposite translations cancel on all homogeneous forms. -/
theorem translationMap_neg :
    (translationMap a).comp (translationMap (-a)) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i r
  rcases i with ⟨i⟩
  fin_cases i <;> ext ⟨j⟩ <;> fin_cases j <;>
    simp [translationMap, Finsupp.linearCombination_single]

/-- Translation is a linear equivalence with the explicit opposite translation as inverse. -/
def translationLinear : (ULift.{u} (Fin 2) →₀ R) ≃ₗ[R] (ULift.{u} (Fin 2) →₀ R) :=
  LinearEquiv.ofLinearMap (translationMap a) (translationMap (-a))
    (translationMap_neg a) (by simpa using translationMap_neg (-a))

/-- The inverse linear equivalence is translation by the opposite coefficient. -/
theorem translationLinear_neg : (translationLinear a).symm = translationLinear (-a) := by
  apply LinearEquiv.ext
  intro v
  rfl

/-- The complete projective translation. -/
def translationProjIso : space R (ULift.{u} (Fin 2)) ≅ space R (ULift.{u} (Fin 2)) :=
  linearIso (translationLinear a).symm

/-- Projective translation retains the original coefficient map. -/
@[reassoc] theorem translationProjIso_base :
    (translationProjIso a).hom ≫ baseProjection R (ULift.{u} (Fin 2)) =
      baseProjection R (ULift.{u} (Fin 2)) :=
  linearIso_baseProjection _

/-- The homogeneous substitution is the specified affine translation. -/
theorem translation_substitution (i : ULift.{u} (Fin 2)) :
    linearSubstitution (translationMap a) (X i) =
      ![X (ULift.up 0), X (ULift.up 1) + C a * X (ULift.up 0)] i.down := by
  rcases i with ⟨i⟩
  fin_cases i <;> simp [linearSubstitution_X, translationMap,
    Finsupp.linearCombination_single, Algebra.smul_def]

/-- Evaluation computes the translation over every affine test ring. -/
theorem translation_evaluation {S : Type u} [CommRing S]
    (f : R →+* S) (x : ULift.{u} (Fin 2) → S) :
    (eval₂Hom f x).comp (linearGradedMap (translationLinear a).toLinearMap).toRingHom =
      eval₂Hom f (fun i =>
        ![x (ULift.up 0), x (ULift.up 1) + f a * x (ULift.up 0)] i.down) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [linearGradedMap, linearSubstitution]
  · intro i
    change eval₂Hom f x (linearSubstitution (translationMap a) (X i)) = _
    rw [translation_substitution]
    rcases i with ⟨i⟩
    fin_cases i <;> simp

/-- Translation commutes with the actual coefficient homomorphism. -/
theorem translation_coefficient {S : Type u} [CommRing S] (f : R →+* S) :
    coefficientMap f (ULift.{u} (Fin 2)) ≫ (translationProjIso a).hom =
      (translationProjIso (f a)).hom ≫ coefficientMap f (ULift.{u} (Fin 2)) := by
  apply linearIso_coefficientMap
  apply changeCoefficients_inverse
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single i r =>
    rcases i with ⟨i⟩
    fin_cases i <;> ext ⟨j⟩ <;> fin_cases j <;>
      simp [translationLinear, translationMap, Finsupp.linearCombination_single,
        changeCoefficients, Finsupp.smul_single, map_add, map_mul]

/-- Opposite translations cancel on the complete projective scheme. -/
theorem translationProjIso_neg :
    (translationProjIso a).hom ≫ (translationProjIso (-a)).hom = 𝟙 _ := by
  change (linearIso (translationLinear a).symm).hom ≫
    (linearIso (translationLinear (-a)).symm).hom = _
  rw [← translationLinear_neg, LinearEquiv.symm_symm]
  exact (linearIso (translationLinear a)).inv_hom_id

end FLT.Mazur.ProjectiveLine
