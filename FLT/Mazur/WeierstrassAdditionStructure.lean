/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalAdditionGluing

/-!
# Addition respects the coefficient scheme

The local laws are algebra homomorphisms over the coefficient ring. Their
coefficient identities descend through the affine and input-product covers,
so the global addition is a morphism over the original base spectrum.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Taking spectra of an algebra homomorphism preserves the coefficient map. -/
theorem specAlgHom_structure {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact f.comp_algebraMap

/-- Every affine-input local law has the same coefficient map as its inclusion. -/
theorem additionCurveChart_structure (i : AdditionChartIndex) :
    additionCurveChart W i ≫ integralCurveStructure W =
      additionChartInclusion W i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W))) := by
  rw [additionCurveChart, Category.assoc, integralCurveChart_structure]
  cases i <;> change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  all_goals exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm

/-- The glued affine-input law is over the coefficient spectrum. -/
theorem affineAdditionToCurve_structure (hΔ : IsUnit W.Δ) :
    affineAdditionToCurve W hΔ ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W))) := by
  apply (additionAffineOpenCover W hΔ).hom_ext
  intro i
  change additionChartInclusion W i ≫ _ = _
  rw [← Category.assoc, additionCurveChart_glued, additionCurveChart_structure]
  rfl

/-- Addition on a mixed input product preserves coefficients. -/
theorem mixedProductAdditionToCurve_structure (hΔ : IsUnit W.Δ) (j k : Fin 3)
    (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2) (ha : j = 2 ∨ k = 2) :
    mixedProductAdditionToCurve W hΔ j k hj hk ha ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W j k))) := by
  apply (mixedProductOpenCover W j k hj hk ha).hom_ext
  intro i
  cases i
  · change projectiveAdditionInclusion W j k 2 ≫ _ = _
    rw [← Category.assoc, mixedProductAdditionToCurve_polynomial,
      Category.assoc, integralCurveChart_structure]
    exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm
  · change Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k 2 2).toRingHom) ≫
      _ = _
    rw [← Category.assoc, mixedProductAdditionToCurve_affine,
      Category.assoc, affineAdditionToCurve_structure]
    exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm

/-- Addition on the full Y-chart input product preserves coefficients. -/
theorem yProductAdditionToCurve_structure (hΔ : IsUnit W.Δ) :
    yProductAdditionToCurve W hΔ ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1))) := by
  apply (yProductOpenCover W).hom_ext
  intro i
  cases i
  · change Spec.map (CommRingCat.ofHom (productOverlapRestriction W 1 1 2 2).toRingHom) ≫
      _ = _
    rw [← Category.assoc, yProductAdditionToCurve_affine,
      Category.assoc, affineAdditionToCurve_structure]
    exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm
  · change projectiveAdditionInclusion W 1 1 2 ≫ _ = _
    rw [← Category.assoc, yProductAdditionToCurve_polynomial,
      Category.assoc, integralCurveChart_structure]
    exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm
  · change infinityAdditionInclusion W ≫ _ = _
    rw [← Category.assoc, yProductAdditionToCurve_infinity,
      Category.assoc, integralCurveChart_structure]
    exact (specAlgHom_structure _).trans (specAlgHom_structure _).symm

/-- Every descended input-chart law is over the same base. -/
theorem integralInputAdditionToCurve_structure (hΔ : IsUnit W.Δ) (b c : Bool) :
    integralInputAdditionToCurve W hΔ b c ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))) := by
  cases b <;> cases c
  · exact mixedProductAdditionToCurve_structure W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl)
  · exact mixedProductAdditionToCurve_structure W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl)
  · exact mixedProductAdditionToCurve_structure W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl)
  · exact yProductAdditionToCurve_structure W hΔ

/-- The global regular addition commutes with the first coefficient projection. -/
theorem integralCurveAddition_structure (hΔ : IsUnit W.Δ) :
    integralCurveAddition W hΔ ≫ integralCurveStructure W =
      pullback.fst (integralCurveStructure W) (integralCurveStructure W) ≫
        integralCurveStructure W := by
  apply (integralCurveProductCover W).hom_ext
  intro p
  change integralCurveProductChart W p.1 p.2 ≫ _ =
    integralCurveProductChart W p.1 p.2 ≫ _
  rw [← Category.assoc, integralCurveProductChart_addition,
    integralInputAdditionToCurve_structure, ← Category.assoc,
    integralCurveProductChart_fst, Category.assoc, integralCurveChart_structure]
  exact (specAlgHom_structure _).symm

/-- Equally, the global addition commutes with the second coefficient projection. -/
theorem integralCurveAddition_structure_snd (hΔ : IsUnit W.Δ) :
    integralCurveAddition W hΔ ≫ integralCurveStructure W =
      pullback.snd (integralCurveStructure W) (integralCurveStructure W) ≫
        integralCurveStructure W :=
  (integralCurveAddition_structure W hΔ).trans pullback.condition

end FLT.Mazur.WeierstrassIntegralChart
