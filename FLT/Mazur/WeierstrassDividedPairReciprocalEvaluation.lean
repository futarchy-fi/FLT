/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPairReciprocalGeometry
public import FLT.Mazur.WeierstrassDividedReciprocalSpecialization

/-!
# Actual pairs factor through the universal divided reciprocal open

The localization map is constructed from the two divided input maps and
invertibility of their divided ordinate difference. No residue or generic
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
  (hu : IsUnit (a (y W s b3 b4 b6) - c (y W s b3 b4 b6)))
local notation "P" => DividedPairRing W s b3 b4 b6
local notation "T" => DividedPairReciprocalRing W s b3 b4 b6
local notation "L" => dividedPairLeft W s b3 b4 b6
local notation "M" => dividedPairRight W s b3 b4 b6
local notation "dy" => L (y W s b3 b4 b6) - M (y W s b3 b4 b6)

/-- The factorization of an actual divided reciprocal pair through the universal source. -/
def dividedPairReciprocalEvaluation : T →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom dy (f := dividedPairEvaluation W s b3 b4 b6 a c) (by
    simpa only [map_sub, dividedPairEvaluation_left, dividedPairEvaluation_right] using hu)

/-- The factorization retains the complete original tensor product map. -/
@[simp] theorem dividedPairReciprocalEvaluation_base (t : P) :
    dividedPairReciprocalEvaluation W s b3 b4 b6 a c hu (algebraMap P T t) =
      dividedPairEvaluation W s b3 b4 b6 a c t := by
  simp only [dividedPairReciprocalEvaluation, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

/-- The first arbitrary divided input survives the new principal-open factorization. -/
theorem dividedPairReciprocalEvaluation_left (t : Coordinate W s b3 b4 b6) :
    dividedPairReciprocalEvaluation W s b3 b4 b6 a c hu (algebraMap P T (L t)) = a t := by
  rw [dividedPairReciprocalEvaluation_base, dividedPairEvaluation_left]

/-- The second arbitrary divided input survives the same factorization. -/
theorem dividedPairReciprocalEvaluation_right (t : Coordinate W s b3 b4 b6) :
    dividedPairReciprocalEvaluation W s b3 b4 b6 a c hu (algebraMap P T (M t)) = c t := by
  rw [dividedPairReciprocalEvaluation_base, dividedPairEvaluation_right]

local notation "O" => DividedPairReciprocalOutputRing W s b3 b4 b6
local notation "g" => dividedPairReciprocalEvaluation W s b3 b4 b6 a c hu
variable (hx : a (x W s b3 b4 b6) = c (x W s b3 b4 b6))

include hx in
/-- Equal abscissae make the actual output ordinate a unit under the constructed evaluation. -/
theorem dividedPairReciprocalEvaluation_ordinate :
    g (dividedReciprocalCoordinates W s b3 b4 b6 L M 1) = -1 := by
  apply dividedReciprocalSpecialization_coordinates W s b3 b4 b6 L M g
  change g (algebraMap P T (L (x W s b3 b4 b6))) =
    g (algebraMap P T (M (x W s b3 b4 b6)))
  rw [dividedPairReciprocalEvaluation_left, dividedPairReciprocalEvaluation_right, hx]

/-- Every unit-ordinate-difference pair with equal abscissae lies in the actual output open. -/
def dividedPairReciprocalInfinityEvaluation : O →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (dividedReciprocalCoordinates W s b3 b4 b6 L M 1)
    (f := g) (by
      rw [dividedPairReciprocalEvaluation_ordinate W s b3 b4 b6 a c hu hx]
      exact isUnit_one.neg)

/-- This second localization still retains the complete original reciprocal map. -/
@[simp] theorem dividedPairReciprocalInfinityEvaluation_base (t : T) :
    dividedPairReciprocalInfinityEvaluation W s b3 b4 b6 a c hu hx (algebraMap T O t) =
      g t := by
  simp only [dividedPairReciprocalInfinityEvaluation, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

/-- Both localization steps retain every function of the first actual divided input. -/
theorem dividedPairReciprocalInfinityEvaluation_left (t : Coordinate W s b3 b4 b6) :
    dividedPairReciprocalInfinityEvaluation W s b3 b4 b6 a c hu hx
        (algebraMap T O (algebraMap P T (L t))) = a t := by
  rw [dividedPairReciprocalInfinityEvaluation_base, dividedPairReciprocalEvaluation_left]

/-- Both localization steps retain every function of the second actual divided input. -/
theorem dividedPairReciprocalInfinityEvaluation_right (t : Coordinate W s b3 b4 b6) :
    dividedPairReciprocalInfinityEvaluation W s b3 b4 b6 a c hu hx
        (algebraMap T O (algebraMap P T (M t))) = c t := by
  rw [dividedPairReciprocalInfinityEvaluation_base, dividedPairReciprocalEvaluation_right]

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The constructed factorization has the normalized original infinity output. -/
theorem dividedPairReciprocalInfinityEvaluation_output :
    (dividedPairReciprocalInfinityEvaluation W s b3 b4 b6 a c hu hx).comp
        (dividedReciprocalOutput W s b3 b4 b6 L M h3 h4 h6) =
      WeierstrassIntegralChart.chartInfinityEvaluation W := by
  apply dividedReciprocalSpecialization_output
  change dividedPairReciprocalInfinityEvaluation W s b3 b4 b6 a c hu hx
      (algebraMap T O (algebraMap P T (L (x W s b3 b4 b6)))) =
    dividedPairReciprocalInfinityEvaluation W s b3 b4 b6 a c hu hx
      (algebraMap T O (algebraMap P T (M (x W s b3 b4 b6))))
  rw [dividedPairReciprocalInfinityEvaluation_left,
    dividedPairReciprocalInfinityEvaluation_right, hx]

end FLT.Mazur.WeierstrassDilatation
