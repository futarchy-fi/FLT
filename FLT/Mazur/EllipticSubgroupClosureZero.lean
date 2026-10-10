/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupAmbientSectionLaws

/-!
# Zero and negation on the actual subgroup closure

The integral zero section factors the original infinity section. The descended
negation acts on every integral subgroup section by its original group inverse.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- Descended negation sends every integral subgroup section to its actual negative section. -/
theorem integralSection_negation (P : H) :
    integralSection A W H P ≫ closureNegation A W H = integralSection A W H (-P) := by
  apply closureToCurve_hom_ext A W H
  rw [Category.assoc, closureNegation_toCurve]
  apply ambientSections_generic_ext A W
  · rw [Category.assoc, Category.assoc, integralCurveNegation_structure,
      closureToCurve_structure, integralSection_toBase, Category.assoc,
      closureToCurve_structure, integralSection_toBase]
  · rw [← Category.assoc _ _ (integralCurveNegation W),
      ← Category.assoc _ _ (integralCurveNegation W), integralSection_generic_toCurve]
    rw [integralSection_generic_toCurve]
    exact (projectiveToIntegral_neg W P.1).symm

/-- The closure zero as a morphism from the unit of the category over the valuation ring. -/
def closureOverZero : 𝟙_ (Over (Spec (.of A))) ⟶ Over.mk (closureToBase A W H 1 2) :=
  Over.homMk (integralSection A W H 0) (integralSection_toBase A W H 0)

omit [Finite H] in
/-- The closure's actual zero section maps to the ambient integral zero. -/
theorem closureOverZero_toCurve :
    closureOverZero A W H ≫ closureOverToCurve A W H 1 2 = integralCurveOverZero W := by
  apply Over.OverMorphism.ext
  exact integralSection_zero_toCurve A W H

/-- The actual descended negation as an endomorphism over the valuation ring. -/
def closureOverNegation : Over.mk (closureToBase A W H 1 2) ⟶
    Over.mk (closureToBase A W H 1 2) :=
  Over.homMk (closureNegation A W H) (closureNegation_toBase A W H)

/-- Zero is fixed by the descended negation on the actual closure. -/
theorem closureOverZero_negation :
    closureOverZero A W H ≫ closureOverNegation A W H = closureOverZero A W H := by
  apply Over.OverMorphism.ext
  change integralSection A W H 0 ≫ closureNegation A W H = integralSection A W H 0
  simpa only [neg_zero] using integralSection_negation A W H 0

end FLT.Mazur.EllipticSubgroupChart
