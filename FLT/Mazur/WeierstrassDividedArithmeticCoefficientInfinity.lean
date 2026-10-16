/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSeparation

/-!
# Infinity exclusions from the original coefficient conditions

The coefficient hypotheses also cover starting depth zero: then the
parameter is a unit and the entire arithmetic base is empty. Thus the
terminal and retained infinity exclusions need no extra positivity assumption.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m k hk

include H
omit [IsDomain R] [IsBezout R] in
/-- Starting depth zero forces every arithmetic coefficient quotient to be the zero ring. -/
theorem arithmeticAtlasCoefficients_quotient_subsingleton (hstart : start = 0) :
    Subsingleton (Quotient R π m) := by
  have hu : IsUnit π := isUnit_iff_dvd_one.mpr (by simpa [hstart] using H.scale_div)
  rcases subsingleton_or_nontrivial (Quotient R π m) with h | h
  · exact h
  · exact False.elim (((hu.map (algebraMap R (Quotient R π m))).not_isNilpotent)
      ⟨m + 1, parameter_pow R π m⟩)

/-- With starting depth zero the actual arithmetic stage is empty under the coefficient rules. -/
theorem arithmeticAtlasCoefficients_stage_isEmpty (hstart : start = 0) :
    IsEmpty (finiteGlobalArithmeticStage hπ data k hk m) := by
  let _ := arithmeticAtlasCoefficients_quotient_subsingleton data H m hstart
  let _ : IsEmpty (Spec (.of (Quotient R π m))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (Quotient R π m)))
  exact Function.isEmpty (finiteGlobalArithmeticStructure hπ data k hk m)

/-- The full terminal node misses infinity under the given coefficient hypotheses at every depth. -/
theorem arithmeticLabeledAtlas_terminal_infinity_disjoint_of_coefficients :
    Disjoint (Set.range (c .terminal)) (Set.range (c .infinity)) := by
  by_cases hp : 0 < start + k
  · exact arithmeticLabeledAtlas_terminal_infinity_disjoint hπ data H m k hk hp
  · let _ := arithmeticAtlasCoefficients_stage_isEmpty hπ data H m k hk (by omega)
    exact Set.disjoint_left.mpr fun z _ _ => isEmptyElim z

/-- Every retained full node misses infinity, including the vacuous zero-start case. -/
theorem arithmeticLabeledAtlas_retained_infinity_disjoint_of_coefficients
    (a : Fin k) (label : Bool) :
    Disjoint (Set.range (c (.retained a label))) (Set.range (c .infinity)) := by
  by_cases hp : 0 < start + a.val
  · exact arithmeticLabeledAtlas_retained_infinity_disjoint hπ data H m k hk a label hp
  · let _ := arithmeticAtlasCoefficients_stage_isEmpty hπ data H m k hk (by omega)
    exact Set.disjoint_left.mpr fun z _ _ => isEmptyElim z

end FLT.Mazur.WeierstrassDividedDepth
