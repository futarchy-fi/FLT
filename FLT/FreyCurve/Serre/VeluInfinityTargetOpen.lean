/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityScaledEquation

/-!
# The final infinity neighborhood and target normalization

Invert the scaled image ordinate, which has value one at source infinity.
Normalizing the proved homogeneous solution now gives a regular target chart map.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The final actual principal neighborhood of source infinity. -/
abbrev InfinityTargetRing := Localization.Away (infinityScaledY E G)

/-- Cache the ring structure of the third localization for bounded instance search. -/
instance infinityTargetRingCommRing : CommRing (InfinityTargetRing E G) :=
  inferInstanceAs (CommRing (Localization.Away (infinityScaledY E G)))

/-- The original infinity point lifts to the final neighborhood. -/
def infinityTargetEvaluation : InfinityTargetRing E G →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (S := InfinityTargetRing E G) (infinityScaledY E G)
    (show IsUnit (infinityKernelEvaluation E G (infinityScaledY E G)) by simp)

@[simp] theorem infinityTargetEvaluation_algebraMap (a : InfinityKernelRing E G) :
    infinityTargetEvaluation E G (algebraMap (InfinityKernelRing E G) (InfinityTargetRing E G) a) =
      infinityKernelEvaluation E G a :=
  IsLocalization.Away.lift_eq _
    (show IsUnit (infinityKernelEvaluation E G (infinityScaledY E G)) by simp) a

/-- The normalizing inverse has value one at source infinity. -/
@[simp] theorem infinityTargetEvaluation_inverse :
    infinityTargetEvaluation E G (IsLocalization.Away.invSelf (infinityScaledY E G)) = 1 := by
  have h := congrArg (infinityTargetEvaluation E G)
    (IsLocalization.Away.mul_invSelf (S := InfinityTargetRing E G) (infinityScaledY E G))
  simpa only [map_mul, map_one, infinityTargetEvaluation_algebraMap,
    infinityScaledY_value, one_mul] using h

/-- The homogeneous target coordinates on the final actual neighborhood. -/
def infinityTargetCoordinates : Fin 3 → InfinityTargetRing E G :=
  (IsLocalization.Away.invSelf (infinityScaledY E G) : InfinityTargetRing E G) •
    (fun i => algebraMap (InfinityKernelRing E G) (InfinityTargetRing E G)
      (![infinityScaledX E G, infinityScaledY E G, infinityV E G] i))

omit [CharZero K] in
/-- The target chart is normalized at its y-coordinate. -/
@[simp] theorem infinityTargetCoordinates_y : infinityTargetCoordinates E G 1 = 1 := by
  change IsLocalization.Away.invSelf (infinityScaledY E G) *
    algebraMap (InfinityKernelRing E G) (InfinityTargetRing E G) (infinityScaledY E G) = 1
  rw [mul_comm, IsLocalization.Away.mul_invSelf]

/-- At source infinity the target coordinates are precisely the original identity. -/
theorem infinityTargetCoordinates_value (i : Fin 3) :
    infinityTargetEvaluation E G (infinityTargetCoordinates E G i) = ![0, 1, 0] i := by
  fin_cases i <;>
    simp [infinityTargetCoordinates, Pi.smul_apply, smul_eq_mul]

/-- The normalized coordinates solve the original target equation in the actual ring. -/
theorem infinityTargetCoordinates_equation (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    ((curve E G).map (algebraMap K (InfinityTargetRing E G))).toProjective.Equation
      (infinityTargetCoordinates E G) := by
  have he := (infinityScaled_equation E G hodd).map
    (algebraMap (InfinityKernelRing E G) (InfinityTargetRing E G))
  have hu : IsUnit (IsLocalization.Away.invSelf (infinityScaledY E G) :
      InfinityTargetRing E G) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨algebraMap _ _ (infinityScaledY E G), by
      rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩
  apply (Projective.equation_smul _ hu).mpr
  simp only [Projective.map, WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq K (InfinityKernelRing E G) (InfinityTargetRing E G)] at he
  exact he

/-- A map from the actual target infinity chart to the constructed source neighborhood. -/
def infinityTargetChart (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    Coordinate (curve E G) 1 →ₐ[K] InfinityTargetRing E G :=
  evaluation (curve E G) 1 (infinityTargetCoordinates E G)
    (infinityTargetCoordinates_equation E G hodd) (infinityTargetCoordinates_y E G)

end WeierstrassCurve.Velu
