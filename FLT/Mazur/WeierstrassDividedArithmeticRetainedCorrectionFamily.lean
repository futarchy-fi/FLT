/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCorrection
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledCharts
public import FLT.Mazur.WeierstrassRetainedCorrectionTransport
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialMobius

/-!
# Full corrections at every original retained depth

The family is built from the actual divided data and coefficient hypotheses.
Consecutive restrictions agree by uniqueness of their full independent roots.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "c" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- The full independently constructed correction at an actual retained depth. -/
def arithmeticRetainedFullCorrection (a : Fin k) : (ChartRing (parameter R π m))ˣ :=
  retainedFactorCorrectionUnit (W.map c) (c π) (c (π ^ (start + a.val)))
    (c (data ⟨a.val + 1, by omega⟩).b3) (c (data ⟨a.val + 1, by omega⟩).b4)
    (c (data ⟨a.val + 1, by omega⟩).b6) J (arithmeticParameterIdeal_nilpotent π m)
    (H.a1_unit.map c) (arithmeticCoefficient_mem π m (H.scale a.val))
    (arithmeticCoefficient_mem π m H.a2_div)
    (arithmeticCoefficient_mem π m (H.b3_div _))
    (arithmeticCoefficient_mem π m (H.b4_div _))
    (arithmeticCoefficient_mem π m (H.b6_div _))

/-- Every full correction commutes with the actual consecutive quotient map. -/
theorem arithmeticRetainedFullCorrection_restriction (a : Fin k) :
    Units.map (ringMap (restriction R π m).toRingHom (parameter R π (m + 1))
        (parameter R π m) (restriction_parameter R π m)).toMonoidHom
        (arithmeticRetainedFullCorrection data H (m + 1) k hk a) =
      arithmeticRetainedFullCorrection data H m k hk a := by
  unfold arithmeticRetainedFullCorrection
  exact retainedFactorCorrectionUnit_map_of_eq (arithmeticParameterIdeal_restriction R π m)
    (arithmeticInitialCurve_restriction R π m W) (restriction_parameter R π m)
    ((restriction R π m).commutes (π ^ (start + a.val)))
    ((restriction R π m).commutes _) ((restriction R π m).commutes _)
    ((restriction R π m).commutes _)

variable [IsDomain R] (hπ : π ≠ 0)

include hπ in
/-- Every consecutive pair in the actual family has the same full Laurent correction. -/
theorem arithmeticRetainedFullCorrection_adjacent (a : ℕ) (ha : a + 1 < k) :
    Units.map (leftLaurentMap (parameter R π m)).toMonoidHom
        (arithmeticRetainedFullCorrection data H m k hk ⟨a, by omega⟩) =
      Units.map (retainedPrecedingEvaluation (parameter R π m)).toMonoidHom
        (arithmeticRetainedFullCorrection data H m k hk ⟨a + 1, ha⟩) :=
  arithmeticRetainedCorrection_adjacent hπ (start + a)
    (data ⟨a + 1, by omega⟩) (data ⟨a + 1 + 1, by omega⟩) m
    H.a1_unit (H.scale a) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
    (H.b3_div _) (H.b4_div _) (H.b6_div _) (H.scale (a + 1))

end FLT.Mazur.WeierstrassDividedDepth
