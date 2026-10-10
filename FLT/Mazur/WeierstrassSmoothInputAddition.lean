/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothYAddition

/-!
# Smooth addition on all four projective input charts

Every Y/Z input-chart pair now has its full smooth law. The affine-overlap
and polynomial restrictions are uniform across the four choices of charts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Addition on the full smooth-input open in each projective product chart. -/
def smoothInputAddition (b c : Bool) :
    (smoothProductChartOpen W b c).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  match b, c with
  | true, true => smoothYAddition W
  | true, false => smoothMixedAddition W true false (.inr rfl)
  | false, true => smoothMixedAddition W false true (.inl rfl)
  | false, false => smoothMixedAddition W false false (.inl rfl)

/-- Every smooth input chart retains the full transported affine formula. -/
@[reassoc] theorem smoothInputAddition_affine (b c : Bool) :
    smoothAffineOverlapToChart W b c ≫ smoothInputAddition W b c =
      smoothAffineOverlapAddition W b c := by
  cases b <;> cases c
  · exact smoothMixedLocal_glued W false false (.inl rfl) true
  · exact smoothMixedLocal_glued W false true (.inl rfl) true
  · exact smoothMixedLocal_glued W true false (.inr rfl) true
  · exact smoothYLocal_glued W .affine

/-- Every smooth input chart retains its original polynomial output-Z formula. -/
@[reassoc] theorem smoothInputAddition_polynomial (b c : Bool) :
    smoothPolynomialToInputs W b c 2 ≫ smoothInputAddition W b c =
      polynomialSmoothChart W (productChartCoordinate b) (productChartCoordinate c) 2 := by
  cases b <;> cases c
  · exact smoothMixedLocal_glued W false false (.inl rfl) false
  · exact smoothMixedLocal_glued W false true (.inl rfl) false
  · exact smoothMixedLocal_glued W true false (.inr rfl) false
  · exact smoothYLocal_glued W .polynomial

/-- The Y/Y member also retains the original infinity formula. -/
@[reassoc] theorem smoothInputAddition_infinity :
    smoothInfinityToInputs W ≫ smoothInputAddition W true true = infinitySmoothChart W :=
  smoothYLocal_glued W .infinity

/-- All four smooth laws preserve their coefficient morphisms. -/
theorem smoothInputAddition_structure (b c : Bool) :
    smoothInputAddition W b c ≫ integralSmoothStructure W =
      (smoothProductChartOpen W b c).ι ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))) := by
  cases b <;> cases c
  · exact smoothMixedAddition_structure W false false (.inl rfl)
  · exact smoothMixedAddition_structure W false true (.inl rfl)
  · exact smoothMixedAddition_structure W true false (.inr rfl)
  · exact smoothYAddition_structure W

end FLT.Mazur.WeierstrassIntegralChart
