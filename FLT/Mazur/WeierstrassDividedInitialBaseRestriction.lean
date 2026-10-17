/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialBaseParameter
public import FLT.Mazur.WeierstrassModificationXArithmeticMobiusParameterRestriction
public import FLT.Mazur.WeierstrassRetainedEdgeUnitNaturality
public import FLT.Mazur.PolygonSmoothingPunctureNaturality

/-!
# The full original initial base parameter respects coefficient quotients

Both the original retained right correction and the inverse Mobius parameter
retain their actual arithmetic coefficients at every order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "a" => Fin.mk 0 (Nat.zero_lt_succ j)
local notation "V" => fun k ↦ arithmeticRetainedFullCorrection data H k (j + 1) hj a
local notation "B" => fun k ↦ arithmeticInitialRightEquiv data H k j hj
local notation "E" => fun k ↦ arithmeticInitialBaseEquiv data H k j hj
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))

/-- The original retained right parameter, including its full inverse, has its quotient square. -/
theorem arithmeticInitialRightEquiv_restriction :
    (coeffMap f).comp (B (m + 1)).toRingHom =
      (B m).toRingHom.comp (coeffMap f) := by
  change (coeffMap f).comp (LaurentUnitPoints.evalUnit
    (retainedFixedRightUnit (parameter R π (m + 1)) (V (m + 1)))).toRingHom =
      (LaurentUnitPoints.evalUnit
        (retainedFixedRightUnit (parameter R π m) (V m))).toRingHom.comp (coeffMap f)
  apply LaurentUnitPoints.evalUnit_coefficients
  apply Units.ext
  change coeffMap f (LaurentPolynomial.T 1 *
    punctureLaurentMap (parameter R π (m + 1)) false (V (m + 1) : ChartRing _)) =
      LaurentPolynomial.T 1 * punctureLaurentMap (parameter R π m) false (V m : ChartRing _)
  rw [map_mul, coeffMap_T_one]
  congr 1
  have hv := congrArg Units.val
    (arithmeticRetainedFullCorrection_restriction data H m (j + 1) hj a)
  have h := DFunLike.congr_fun (ringMap_punctureLaurent f
    (parameter R π (m + 1)) (parameter R π m) (restriction_parameter R π m) false)
      (V (m + 1) : ChartRing _)
  exact h.symm.trans (congrArg (punctureLaurentMap (parameter R π m) false) hv)

/-- The complete original base parameter follows the original adjacent coefficient quotient. -/
theorem arithmeticInitialBaseEquiv_restriction :
    (coeffMap f).comp (E (m + 1)).toRingHom =
      (E m).toRingHom.comp (coeffMap f) := by
  unfold arithmeticInitialBaseEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticInitialRightEquiv_restriction data H m j hj
  · exact symm_naturality f _ _ (arithmeticInitialMobiusEquiv_restriction π m W (π ^ 1)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _))

end FLT.Mazur.WeierstrassDividedDepth
