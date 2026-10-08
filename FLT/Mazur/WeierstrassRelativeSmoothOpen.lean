/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralSmooth
public import FLT.Mazur.WeierstrassIntegralFinitePresentation

/-!
# The relative smooth open without a discriminant assumption

The actual relative smooth locus exists for every integral cubic. Every free
Jacobian localization maps into it, including in bad reduction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual relative smooth open of the original glued cubic. -/
abbrev integralSmoothOpen : (integralCurve W).Opens :=
  (integralCurveStructure W).smoothLocus

/-- The structure map of the relative smooth locus. -/
abbrev integralSmoothStructure : (integralSmoothOpen W).toScheme ⟶ Spec (.of R) :=
  (integralSmoothOpen W).ι ≫ integralCurveStructure W

/-- The relative smooth locus is smooth over the original coefficient ring. -/
instance integralSmoothStructure_smooth : Smooth (integralSmoothStructure W) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  exact iff_of_true x.property (Set.mem_univ x)

/-- Every free-derivative localization lands in the relative smooth locus of its chart. -/
theorem chartPartial_range_smooth (j i : Fin 3) (hij : i ≠ j) :
    Set.range (PrincipalAffineRefinement.inclusion (chartPartial W j i)) ⊆
      (chartStructure W j).smoothLocus := by
  let _ := chartPartial_structure_smooth_dimension W j i hij
  let _ := SmoothOfRelativeDimension.smooth 1
    (PrincipalAffineRefinement.inclusion (chartPartial W j i) ≫ chartStructure W j)
  rintro _ ⟨x, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq
    (PrincipalAffineRefinement.inclusion (chartPartial W j i)) (chartStructure W j)
  rw [Scheme.Hom.smoothLocus_eq_top
    (PrincipalAffineRefinement.inclusion (chartPartial W j i) ≫ chartStructure W j)] at h
  exact h.ge (Set.mem_univ x)

/-- The global smooth open restricts on every normalized chart to its actual smooth locus. -/
theorem integralCurveChart_preimage_smooth (j : Fin 3) :
    integralCurveChart W j ⁻¹ᵁ integralSmoothOpen W = (chartStructure W j).smoothLocus := by
  simp only [integralSmoothOpen, Scheme.Hom.preimage_smoothLocus_eq,
    integralCurveChart_structure]

/-- The explicit derivative chart inclusion lands in the global relative smooth open. -/
theorem chartPartial_global_range_smooth (j i : Fin 3) (hij : i ≠ j) :
    Set.range (PrincipalAffineRefinement.inclusion (chartPartial W j i) ≫
      integralCurveChart W j) ⊆ integralSmoothOpen W := by
  rintro _ ⟨x, rfl⟩
  have h := chartPartial_range_smooth W j i hij ⟨x, rfl⟩
  rw [← integralCurveChart_preimage_smooth] at h
  exact h

/-- The actual derivative localization as an open chart of the smooth locus. -/
def chartPartialToSmooth (j i : Fin 3) (hij : i ≠ j) :
    Spec (.of (Localization.Away (chartPartial W j i))) ⟶
      (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι
    (PrincipalAffineRefinement.inclusion (chartPartial W j i) ≫ integralCurveChart W j)
    (by rw [Scheme.Opens.range_ι]; exact chartPartial_global_range_smooth W j i hij)

/-- The lifted chart retains the original localization and cubic embedding. -/
@[reassoc (attr := simp)] theorem chartPartialToSmooth_inclusion
    (j i : Fin 3) (hij : i ≠ j) :
    chartPartialToSmooth W j i hij ≫ (integralSmoothOpen W).ι =
      PrincipalAffineRefinement.inclusion (chartPartial W j i) ≫ integralCurveChart W j :=
  IsOpenImmersion.lift_fac _ _ _

/-- Each derivative chart is an open immersion in the actual relative smooth locus. -/
instance chartPartialToSmooth_isOpenImmersion (j i : Fin 3) (hij : i ≠ j) :
    IsOpenImmersion (chartPartialToSmooth W j i hij) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

end FLT.Mazur.WeierstrassIntegralChart
