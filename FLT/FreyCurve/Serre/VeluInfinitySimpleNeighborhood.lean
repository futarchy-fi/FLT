/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityLinearFactor
public import FLT.FreyCurve.Serre.VeluInfinityNeighborhoodIdeal

/-!
# A neighborhood where the original Vélu parameter has a simple zero

Invert the explicit linear factor after normalizing the target chart.
The original identity lifts to this neighborhood and its full ideal is (u).
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart FLT.Mazur.LocalizationEvaluationKernel

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] infinityTargetCoordinates infinityTargetChart

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The original linear factor on the normalized target-chart neighborhood. -/
def infinityTargetXFactor : InfinityTargetRing E G :=
  algebraMap (InfinityKernelRing E G) _ (infinityXFactor E G)

/-- The factor being inverted still has value one at the original identity. -/
@[simp] theorem infinityTargetXFactor_value :
    infinityTargetEvaluation E G (infinityTargetXFactor E G) = 1 := by
  simp [infinityTargetXFactor]

/-- An actual principal neighborhood on which the original target parameter is simple. -/
abbrev InfinitySimpleRing := Localization.Away (infinityTargetXFactor E G)

/-- Cache the final localization ring structure to bound later elaboration. -/
instance infinitySimpleRingCommRing : CommRing (InfinitySimpleRing E G) :=
  inferInstanceAs (CommRing (Localization.Away (infinityTargetXFactor E G)))

/-- The original identity extends over the additional localization. -/
def infinitySimpleEvaluation : InfinitySimpleRing E G →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (S := InfinitySimpleRing E G) (infinityTargetXFactor E G)
    (show IsUnit (infinityTargetEvaluation E G (infinityTargetXFactor E G)) by simp)

@[simp] theorem infinitySimpleEvaluation_algebraMap (a : InfinityTargetRing E G) :
    infinitySimpleEvaluation E G (algebraMap _ (InfinitySimpleRing E G) a) =
      infinityTargetEvaluation E G a :=
  IsLocalization.Away.lift_eq _
    (show IsUnit (infinityTargetEvaluation E G (infinityTargetXFactor E G)) by simp) a

/-- The same original source parameter on the final simple neighborhood. -/
def infinitySimpleU : InfinitySimpleRing E G :=
  algebraMap (InfinityTargetRing E G) _ (infinityTargetU E G)

/-- The full original identity ideal remains principal on the smaller neighborhood. -/
theorem infinitySimpleEvaluation_ker :
    RingHom.ker (infinitySimpleEvaluation E G).toRingHom = Ideal.span {infinitySimpleU E G} :=
  ker_eq_span (Submonoid.powers (infinityTargetXFactor E G))
    (infinityTargetEvaluation E G).toRingHom (infinitySimpleEvaluation E G).toRingHom
    (infinitySimpleEvaluation_algebraMap E G) _ (infinityTargetEvaluation_ker E G)

/-- The actual original target chart map restricted to the additional neighborhood. -/
def infinitySimpleChart (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    Coordinate (curve E G) 1 →ₐ[K] InfinitySimpleRing E G :=
  (IsScalarTower.toAlgHom K (InfinityTargetRing E G) (InfinitySimpleRing E G)).comp
    (infinityTargetChart E G hodd)

/-- Evaluation of the restricted original chart map is the original target identity. -/
theorem infinitySimpleChart_evaluation (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    (infinitySimpleEvaluation E G).comp (infinitySimpleChart E G hodd) =
      infinityEvaluation (curve E G) := by
  apply hom_ext (S := K) (curve E G) 1
  intro i
  change infinitySimpleEvaluation E G
    (algebraMap (InfinityTargetRing E G) _ (infinityTargetChart E G hodd (coord _ 1 i))) = _
  rw [infinitySimpleEvaluation_algebraMap, infinityTargetChart, evaluation_coord,
    infinityTargetCoordinates_value]
  exact (evaluation_coord _ _ _ _ _ _).symm

end WeierstrassCurve.Velu
