/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineAdditionDomain
public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# Regular affine-input addition without good reduction

The already proved overlap identities glue all four local formulas on their
actual union. This gives regular addition on a domain containing all pairs
with nonsingular first input, including on singular cubics.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original chart laws agree on pullbacks taken inside the regular addition domain. -/
theorem additionCurveChart_domain_compatibility (i j : AdditionChartIndex) :
    pullback.fst (additionChartToDomain W i) (additionChartToDomain W j) ≫
        additionCurveChart W i =
      pullback.snd (additionChartToDomain W i) (additionChartToDomain W j) ≫
        additionCurveChart W j := by
  apply additionCurveChart_commonScheme
  rw [← additionChartToDomain_inclusion, ← additionChartToDomain_inclusion,
    ← Category.assoc, pullback.condition, Category.assoc]

/-- The regular partial addition on the affine product, for arbitrary coefficients. -/
def affinePartialAddition : (affineAdditionDomain W).toScheme ⟶ integralCurve W :=
  (affineAdditionDomainCover W).glueMorphisms (additionCurveChart W)
    (additionCurveChart_domain_compatibility W)

/-- The glued partial addition retains all four original regular local formulas. -/
@[reassoc] theorem additionChartToDomain_addition (i : AdditionChartIndex) :
    additionChartToDomain W i ≫ affinePartialAddition W = additionCurveChart W i :=
  (affineAdditionDomainCover W).ι_glueMorphisms _ _ i

/-- Partial addition is over the original coefficient spectrum. -/
theorem affinePartialAddition_structure :
    affinePartialAddition W ≫ integralCurveStructure W =
      (affineAdditionDomain W).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W))) := by
  apply (affineAdditionDomainCover W).hom_ext
  intro i
  change additionChartToDomain W i ≫ _ = additionChartToDomain W i ≫ _
  rw [← Category.assoc, additionChartToDomain_addition, additionCurveChart_structure,
    additionChartToDomain_inclusion_assoc]

/-- In good reduction the new partial law is the restriction of the previously glued addition. -/
theorem affinePartialAddition_goodReduction (hΔ : IsUnit W.Δ) :
    affinePartialAddition W = (affineAdditionDomain W).ι ≫ affineAdditionToCurve W hΔ := by
  apply (affineAdditionDomainCover W).hom_ext
  intro i
  change additionChartToDomain W i ≫ _ = additionChartToDomain W i ≫ _
  rw [additionChartToDomain_addition, additionChartToDomain_inclusion_assoc,
    additionCurveChart_glued]

/-- The chart formulas uniquely determine addition on this actual domain. -/
theorem affinePartialAddition_unique (f : (affineAdditionDomain W).toScheme ⟶ integralCurve W)
    (hf : ∀ i, additionChartToDomain W i ≫ f = additionCurveChart W i) :
    f = affinePartialAddition W := by
  apply (affineAdditionDomainCover W).hom_ext
  intro i
  exact (hf i).trans (additionChartToDomain_addition W i).symm

end FLT.Mazur.WeierstrassIntegralChart
