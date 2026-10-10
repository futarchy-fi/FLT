/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupAmbientChartPreimage
public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover

/-!
# The actual subgroup closure is a closed subscheme of the cubic

The Y/Z cover pulls back to the constructed closure charts. Their kernel
quotient inclusions are closed immersions, and this property descends on the target.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- The original Y/Z closure morphism is a closed immersion into the actual cubic. -/
instance closureToCurve_isClosedImmersion : IsClosedImmersion (closureToCurve A W H 1 2) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (integralCurveTwoChartCover W)
  intro b
  cases b
  · change IsClosedImmersion (pullback.snd (closureToCurve A W H 1 2) (integralCurveChart W 2))
    rw [← (closureAmbientChart_right_isPullback A W H 1 2).flip.isoPullback_inv_snd]
    infer_instance
  · change IsClosedImmersion (pullback.snd (closureToCurve A W H 1 2) (integralCurveChart W 1))
    rw [← (closureAmbientChart_left_isPullback A W H 1 2).flip.isoPullback_inv_snd]
    infer_instance

/-- Maps into the actual closure are determined by their ambient cubic morphisms. -/
theorem closureToCurve_hom_ext {X : Scheme} (f g : X ⟶ gluedClosure A W H 1 2)
    (h : f ≫ closureToCurve A W H 1 2 = g ≫ closureToCurve A W H 1 2) : f = g :=
  (cancel_mono (closureToCurve A W H 1 2)).mp h

/-- Ambient morphisms whose equations contain the closure ideal factor through this closure. -/
def closureToCurveLift {X : Scheme} (f : X ⟶ integralCurve W)
    (h : (closureToCurve A W H 1 2).ker ≤ f.ker) : X ⟶ gluedClosure A W H 1 2 :=
  IsClosedImmersion.lift (closureToCurve A W H 1 2) f h

/-- The constructed factorization preserves the given ambient morphism. -/
@[reassoc] theorem closureToCurveLift_inclusion {X : Scheme} (f : X ⟶ integralCurve W)
    (h : (closureToCurve A W H 1 2).ker ≤ f.ker) :
    closureToCurveLift A W H f h ≫ closureToCurve A W H 1 2 = f :=
  IsClosedImmersion.lift_fac _ _ _

end FLT.Mazur.EllipticSubgroupChart
