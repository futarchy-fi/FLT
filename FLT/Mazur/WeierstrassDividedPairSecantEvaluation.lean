/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairSecant

/-!
# Actual pairs factor through the universal divided secant open

The localization map is constructed from the two divided input maps and
invertibility of their divided abscissa difference. No residue or generic
factorization is assumed as additional data.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (hu : IsUnit (a (x W s b3 b4 b6) - c (x W s b3 b4 b6)))
local notation "P" => DividedPairRing W s b3 b4 b6
local notation "T" => DividedPairSecantRing W s b3 b4 b6
local notation "L" => dividedPairLeft W s b3 b4 b6
local notation "M" => dividedPairRight W s b3 b4 b6
local notation "dx" => L (x W s b3 b4 b6) - M (x W s b3 b4 b6)

/-- The factorization of an actual divided secant pair through the universal source. -/
def dividedPairSecantEvaluation : T →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom dx (f := dividedPairEvaluation W s b3 b4 b6 a c) (by
    simpa only [map_sub, dividedPairEvaluation_left, dividedPairEvaluation_right] using hu)

/-- The factorization retains the complete original tensor product map. -/
@[simp] theorem dividedPairSecantEvaluation_base (t : P) :
    dividedPairSecantEvaluation W s b3 b4 b6 a c hu (algebraMap P T t) =
      dividedPairEvaluation W s b3 b4 b6 a c t := by
  simp only [dividedPairSecantEvaluation, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

/-- The first arbitrary divided input survives the new principal-open factorization. -/
theorem dividedPairSecantEvaluation_left (t : Coordinate W s b3 b4 b6) :
    dividedPairSecantEvaluation W s b3 b4 b6 a c hu (algebraMap P T (L t)) = a t := by
  rw [dividedPairSecantEvaluation_base, dividedPairEvaluation_left]

/-- The second arbitrary divided input survives the same factorization. -/
theorem dividedPairSecantEvaluation_right (t : Coordinate W s b3 b4 b6) :
    dividedPairSecantEvaluation W s b3 b4 b6 a c hu (algebraMap P T (M t)) = c t := by
  rw [dividedPairSecantEvaluation_base, dividedPairEvaluation_right]

/-- The evaluated slope is determined by the divided input difference, without a scale inverse. -/
theorem dividedPairSecantEvaluation_slope :
    dividedPairSecantEvaluation W s b3 b4 b6 a c hu
        (dividedSecantSlope W s b3 b4 b6 L M) *
        (a (x W s b3 b4 b6) - c (x W s b3 b4 b6)) =
      a (y W s b3 b4 b6) - c (y W s b3 b4 b6) := by
  have hleft (t) : dividedPairSecantEvaluation W s b3 b4 b6 a c hu
      (IsScalarTower.toAlgHom R P T (L t)) = a t :=
    dividedPairSecantEvaluation_left W s b3 b4 b6 a c hu t
  have hright (t) : dividedPairSecantEvaluation W s b3 b4 b6 a c hu
      (IsScalarTower.toAlgHom R P T (M t)) = c t :=
    dividedPairSecantEvaluation_right W s b3 b4 b6 a c hu t
  have h := congrArg (dividedPairSecantEvaluation W s b3 b4 b6 a c hu)
    (dividedSecantSlope_relation W s b3 b4 b6 L M)
  simpa only [map_mul, map_sub, AlgHom.comp_apply, hleft, hright] using h

end FLT.Mazur.WeierstrassDilatation
