/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFiniteChartDescent
public import FLT.Mazur.WeierstrassSmoothSevenPoints

/-!
# Associativity of the full relative smooth Weierstrass law

Simultaneous pullbacks of the Y/Z atlas present the three original inputs,
both intermediate sums and both final outputs. On affine restrictions the
five regular coordinates give injective localization descent. This proves
associativity over every coefficient ring and at every reduction type.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual iterated sums of the full relative smooth Weierstrass law agree globally. -/
theorem smoothFactorAddition_assoc :
    smoothFactorTripleAddLeft W = smoothFactorTripleAddRight W := by
  apply finiteCurveCharts_hom_ext W 7 (smoothTripleSevenPoint W)
  intro X t ht b p hp
  let _ := ht
  apply Scheme.Cover.hom_ext X.affineCover
  intro i
  let a := X.affineCover.f i
  have he : ∀ j, (a ≫ p j) ≫ integralCurveChart W (productChartCoordinate (b j)) =
      (a ≫ t) ≫ smoothTripleSevenPoint W j := by
    intro j
    rw [Category.assoc, hp, Category.assoc]
  simpa only [Category.assoc] using
    smoothFactorTripleAdd_of_sevenCharts W (a ≫ t) b (fun j => a ≫ p j) he

end FLT.Mazur.WeierstrassIntegralChart
