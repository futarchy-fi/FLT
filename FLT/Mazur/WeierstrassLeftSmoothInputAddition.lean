/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInputRestrictions

/-!
# Enlarged addition on every projective input chart

All four left smooth input opens carry curve-valued addition. Its affine and
polynomial restrictions are uniform and impose no smoothness on the second input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Addition on the complete left smooth open of any projective input chart. -/
def leftSmoothInputAddition (b c : Bool) :
    (leftSmoothProductChartOpen W b c).toScheme ⟶ integralCurve W :=
  match b, c with
  | true, true => leftSmoothYAddition W
  | true, false => leftSmoothMixedAddition W true false (.inr rfl)
  | false, true => leftSmoothMixedAddition W false true (.inl rfl)
  | false, false => leftSmoothMixedAddition W false false (.inl rfl)

/-- A mixed chart's uniform law is its glued two-domain law. -/
theorem leftSmoothInputAddition_mixed (b c : Bool) (ha : b = false ∨ c = false) :
    leftSmoothInputAddition W b c = leftSmoothMixedAddition W b c ha := by
  rcases ha with rfl | rfl
  · cases c <;> rfl
  · cases b <;> rfl

/-- All four laws retain the enlarged affine formula on any common input scheme. -/
theorem leftSmoothInputAddition_affine (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (g : X ⟶ (leftSmoothAffineOverlapOpen W b c).toScheme)
    (h : f ≫ (leftSmoothProductChartOpen W b c).ι =
      g ≫ leftSmoothAffineOverlapInput W b c) :
    f ≫ leftSmoothInputAddition W b c = g ≫ leftSmoothAffineOverlapAddition W b c := by
  cases b <;> cases c
  · exact leftSmoothMixedAddition_affine W false false (.inl rfl) f g h
  · exact leftSmoothMixedAddition_affine W false true (.inl rfl) f g h
  · exact leftSmoothMixedAddition_affine W true false (.inr rfl) f g h
  · exact leftSmoothYAddition_affine W f g h

/-- All four laws retain the polynomial output-Z formula on any common input scheme. -/
theorem leftSmoothInputAddition_polynomial (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate b) (productChartCoordinate c) 2)))
    (h : f ≫ (leftSmoothProductChartOpen W b c).ι = g ≫
      projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2) :
    f ≫ leftSmoothInputAddition W b c =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate b) (productChartCoordinate c) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  cases b <;> cases c
  · exact leftSmoothMixedAddition_polynomial W false false (.inl rfl) f g h
  · exact leftSmoothMixedAddition_polynomial W false true (.inl rfl) f g h
  · exact leftSmoothMixedAddition_polynomial W true false (.inr rfl) f g h
  · exact leftSmoothYAddition_polynomial W f g h

/-- The actual inclusion of a left smooth chart into the global input product. -/
def leftSmoothProductChartInput (b c : Bool) :
    (leftSmoothProductChartOpen W b c).toScheme ⟶ integralCurveProduct W :=
  (leftSmoothProductChartOpen W b c).ι ≫ integralCurveProductChart W b c

/-- Restricting to left smooth inputs preserves the open chart embedding. -/
instance leftSmoothProductChartInput_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (leftSmoothProductChartInput W b c) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Normalizing both inputs into the affine chart preserves their global input pair. -/
@[reassoc] theorem leftSmoothAffineOverlapToInputs_global (b c : Bool) :
    leftSmoothAffineOverlapToInputs W b c ≫ (leftSmoothAffineInputOpen W).ι ≫
        integralCurveProductChart W false false =
      leftSmoothAffineOverlapInput W b c ≫ integralCurveProductChart W b c := by
  rw [leftSmoothAffineOverlapToInputs_inclusion_assoc, leftSmoothAffineOverlapInput,
    Category.assoc]
  exact congrArg (fun f => (leftSmoothAffineOverlapOpen W b c).ι ≫ f)
    (integralProductOverlap_condition W b c false false).symm

end FLT.Mazur.WeierstrassIntegralChart
