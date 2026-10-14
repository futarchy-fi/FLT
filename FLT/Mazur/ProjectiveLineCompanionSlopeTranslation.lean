/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineHomogeneousReversal
public import FLT.Mazur.ProjectiveLineSlopeNormalization

/-!
# Companion-root translation of the complete ordered slope line

Translation by the tangent unit changes the slope normalization for a into
that for -a followed by endpoint reversal, including the point at infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FLT.Mazur.ProjectiveLine
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- Translation by the tangent unit on the entire glued projective line. -/
def companionSlopeTranslation : scheme K ≅ scheme K :=
  homogeneousIso K ≪≫ translationProjIso (a : K) ≪≫ (homogeneousIso K).symm

/-- The complete slope translation preserves the coefficient field. -/
@[reassoc] theorem companionSlopeTranslation_base :
    (companionSlopeTranslation a).hom ≫ toBase K = toBase K := by
  simp only [companionSlopeTranslation, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    homogeneousIso_inv_base, translationProjIso_base, homogeneousIso_base]

/-- The two signed ordered normalizations differ by translation and homogeneous reversal. -/
@[reassoc] theorem companionSlopeTranslation_projective :
    (translationProjIso (a : K)).hom ≫ (slopeNormalizationProjIso (-a)).hom =
      (slopeNormalizationProjIso a).hom ≫ (reversalProjIso K).hom := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  simp only [← Proj.map_comp]
  congr 1
  apply GradedRingHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [linearGradedMap, linearSubstitution]
  · intro i
    change linearSubstitution (translationMap (a : K))
        (linearSubstitution (slopeNormalizationMap (-a)) (X i)) =
      linearSubstitution (slopeNormalizationMap a)
        (linearSubstitution (reversalMap K) (X i))
    rw [slopeNormalization_substitution, reversal_substitution]
    rcases i with ⟨i⟩
    fin_cases i <;>
      simp [-linearSubstitution_X, translation_substitution, slopeNormalization_substitution,
        show ∀ c, linearSubstitution (translationMap (a : K)) (C c) = C c from
          fun c => AlgHom.commutes _ c, add_comm]

/-- The actual complete slope translation becomes reversal in ordered polygon coordinates. -/
@[reassoc] theorem companionSlopeTranslation_normalization :
    (companionSlopeTranslation a).hom ≫ (slopeNormalizationIso (-a)).hom =
      (slopeNormalizationIso a).hom ≫ endpointReversal K := by
  have hr : endpointReversal K =
      (homogeneousIso K).hom ≫ (reversalProjIso K).hom ≫ (homogeneousIso K).inv := by
    rw [← Category.assoc, homogeneousIso_reversal, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [companionSlopeTranslation, slopeNormalizationIso, Iso.trans_hom,
    Iso.symm_hom, hr, Category.assoc, Iso.inv_hom_id_assoc]
  rw [companionSlopeTranslation_projective_assoc]

/-- On the whole affine chart the translation is the actual substitution z ↦ z+a. -/
@[reassoc] theorem companionSlopeTranslation_left :
    left K ≫ (companionSlopeTranslation a).hom =
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (Polynomial.X + Polynomial.C (a : K))).toRingHom) ≫ left K := by
  have H := unitChartPoint_linearIso_of_eval (translationLinear (a : K)).symm
    (Polynomial.C : K →+* Polynomial K)
    (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial K) i.down) _
    (translation_evaluation (a : K) (Polynomial.C : K →+* Polynomial K)
      (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial K) i.down))
    (ULift.up 0) (ULift.up 0) 1 1 rfl rfl
  have hl := homogeneousPoint_left K (Polynomial.C : K →+* Polynomial K)
    (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial K) i.down) 1 rfl
  have he : Polynomial.eval₂RingHom (Polynomial.C : K →+* Polynomial K) Polynomial.X =
      RingHom.id _ := by ext <;> simp
  simp only [inv_one, Units.val_one, one_mul, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, he, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at hl
  nth_rw 1 [← hl]
  rw [companionSlopeTranslation]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  erw [H]
  rw [homogeneousPoint_left]
  simp only [inv_one, Units.val_one, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, mul_one]
  rfl

end FLT.Mazur.ProjectiveLine
