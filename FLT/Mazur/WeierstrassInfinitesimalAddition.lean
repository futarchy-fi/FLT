/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinitesimalSlopeLift

/-!
# Actual addition on infinitesimal identity-chart sections

Infinitesimal pairs factor through both localizations defining the regular
infinity law. That original chart law sends their parameters to their sum.
This supplies the local computation needed for prime-to-characteristic torsion
rigidity, before passing from charts to arbitrary scheme-valued group points.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal A) (hI : I ^ 2 = ⊥) (x y : I)

/-- Infinitesimal pairs also lift through the actual output normalization. -/
def infinitesimalAdditionLift : InfinityAdditionOpen W →ₐ[R] A :=
  IsLocalization.Away.liftAlgHom (infinityOutputCoordinates W 1)
    (show IsUnit (infinitesimalSlopeLift W I hI x y (infinityOutputCoordinates W 1)) by
      rw [infinitesimalSlopeLift_output]
      exact infinitySquareZero_output_unit (W.map (algebraMap R A)) I hI x.property y.property)

/-- The normalized lift retains the original slope-domain point. -/
@[simp] theorem infinitesimalAdditionLift_comp :
    (infinitesimalAdditionLift W I hI x y).comp (infinityOutputRestriction W) =
      infinitesimalSlopeLift W I hI x y := by
  apply AlgHom.ext
  intro a
  change infinitesimalAdditionLift W I hI x y (algebraMap _ _ a) = _
  simp only [infinitesimalAdditionLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The final lift retains the entire original pair, including both coordinate maps. -/
theorem infinitesimalAdditionLift_restriction :
    (infinitesimalAdditionLift W I hI x y).comp (infinityAdditionRestriction W) =
      infinitesimalPairEvaluation W I hI x y := by
  rw [infinityAdditionRestriction, ← AlgHom.comp_assoc, infinitesimalAdditionLift_comp,
    infinitesimalSlopeLift_comp]

/-- The original regular addition chart adds the infinitesimal parameters. -/
theorem infinityAdditionChart_infinitesimal :
    (infinitesimalAdditionLift W I hI x y).comp (infinityAdditionChart W) =
      (infinitesimalChartPoint W I hI (x + y)).val := by
  let F := infinitesimalAdditionLift W I hI x y
  have hr (a) : F (infinityOutputRestriction W a) = infinitesimalSlopeLift W I hI x y a :=
    DFunLike.congr_fun (infinitesimalAdditionLift_comp W I hI x y) a
  have hi := congrArg F (infinityOutputInverse_mul W)
  simp only [map_mul, map_one, hr, infinitesimalSlopeLift_output] at hi
  have hn := infinitySquareZero_normalized (W.map (algebraMap R A)) I hI
    x.property y.property hi
  apply hom_ext
  intro i
  have he := congrArg F (infinityAdditionChart_coord W i)
  simp only [map_mul, hr, infinitesimalSlopeLift_output] at he
  change F (infinityAdditionChart W (coord W 1 i)) = _
  rw [he]
  exact (congrFun hn i).trans (evaluation_coord W 1 _
    (infinitesimalChart_equation W I hI (x + y)) rfl i).symm

/-- In particular, the actual doubling chart doubles the infinitesimal X coordinate. -/
theorem infinityAdditionChart_infinitesimal_double :
    (infinitesimalAdditionLift W I hI x x).comp (infinityAdditionChart W) =
      (infinitesimalChartPoint W I hI (2 • x)).val := by
  simpa only [two_smul] using infinityAdditionChart_infinitesimal W I hI x x

end FLT.Mazur.WeierstrassIntegralChart
