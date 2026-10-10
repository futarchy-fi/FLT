/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveChartEquation

/-!
# Cubic transition law for the actual projective equations

The defining equations on two ambient affine charts differ by the cube of the
invertible coordinate ratio. This is the coefficient identity needed to glue
multiplication by the cubic from O(-3) to O, with the original local kernels.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluate the homogeneous cubic in any coefficient algebra. -/
theorem cubic_aeval {S : Type*} [CommRing S] [Algebra R S] (v : Fin 3 → S) :
    aeval v W.toProjective.polynomial =
      v 1 ^ 2 * v 2 + algebraMap R S W.a₁ * v 0 * v 1 * v 2 +
        algebraMap R S W.a₃ * v 1 * v 2 ^ 2 -
        (v 0 ^ 3 + algebraMap R S W.a₂ * v 0 ^ 2 * v 2 +
          algebraMap R S W.a₄ * v 0 * v 2 ^ 2 + algebraMap R S W.a₆ * v 2 ^ 3) := by
  simp [WeierstrassCurve.Projective.polynomial]

/-- Scalar rescaling acts on the cubic equation with weight three over any ring. -/
theorem cubic_aeval_scale {S : Type*} [CommRing S] [Algebra R S]
    (v : Fin 3 → S) (a : S) :
    aeval (fun i => a * v i) W.toProjective.polynomial =
      a ^ 3 * aeval v W.toProjective.polynomial := by
  rw [cubic_aeval, cubic_aeval]
  ring

/-- On each genuine ambient overlap, the two equations differ by the cubed coordinate ratio. -/
theorem projectiveChartEquation_transition (j k : Fin 3) :
    ProjectiveSpace.chartOverlapLeft R (Fin 3) j k (projectiveChartEquation W j) =
      ProjectiveSpace.chartOverlapLeft R (Fin 3) j k
        (ProjectiveSpace.coordinate R (Fin 3) j k) ^ 3 *
        ProjectiveSpace.chartOverlapRight R (Fin 3) j k (projectiveChartEquation W k) := by
  have hl : (ProjectiveSpace.chartOverlapLeft R (Fin 3) j k).comp
      (aeval (ProjectiveSpace.coordinate R (Fin 3) j)) =
      aeval (fun i => ProjectiveSpace.chartOverlapLeft R (Fin 3) j k
        (ProjectiveSpace.coordinate R (Fin 3) j k) *
        ProjectiveSpace.chartOverlapRight R (Fin 3) j k
          (ProjectiveSpace.coordinate R (Fin 3) k i)) := by
    ext i : 1
    simpa only [AlgHom.comp_apply, aeval_X, mul_comm] using
      ProjectiveSpace.chartOverlap_coordinate R (Fin 3) j k i
  have hr : (ProjectiveSpace.chartOverlapRight R (Fin 3) j k).comp
      (aeval (ProjectiveSpace.coordinate R (Fin 3) k)) =
      aeval (fun i => ProjectiveSpace.chartOverlapRight R (Fin 3) j k
        (ProjectiveSpace.coordinate R (Fin 3) k i)) := by
    ext i : 1
    simp only [AlgHom.comp_apply, aeval_X]
  change ((ProjectiveSpace.chartOverlapLeft R (Fin 3) j k).comp
    (aeval (ProjectiveSpace.coordinate R (Fin 3) j))) W.toProjective.polynomial =
      _ ^ 3 * ((ProjectiveSpace.chartOverlapRight R (Fin 3) j k).comp
        (aeval (ProjectiveSpace.coordinate R (Fin 3) k))) W.toProjective.polynomial
  rw [hl, hr, cubic_aeval_scale]

/-- The transition factor is a unit, including over nonreduced coefficient rings. -/
theorem projectiveChartEquation_transition_isUnit (j k : Fin 3) :
    IsUnit (ProjectiveSpace.chartOverlapLeft R (Fin 3) j k
      (ProjectiveSpace.coordinate R (Fin 3) j k) ^ 3) :=
  (ProjectiveSpace.isUnit_ratio R (Fin 3) j k).pow 3

end FLT.Mazur.WeierstrassIntegralChart
