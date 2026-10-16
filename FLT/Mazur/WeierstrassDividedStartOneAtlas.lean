/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedStartOneData
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledCharts

/-!
# Integral arithmetic coefficients for the depth-one extension

Every earlier divided coefficient retains the terminal coefficient's
uniformizer divisibility. Thus extending a positive family to depth one
constructs the hypotheses of the arithmetic atlas without a unit assumption
on the original quotient of smoothing parameters.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (hstart : 0 < start)

include H in
/-- The extended depth-one family satisfies all actual arithmetic coefficient conditions. -/
theorem startOneAtlasCoefficients : ArithmeticAtlasCoefficients (startOneData data hstart) where
  a1_unit := H.a1_unit
  scale_div := by simp
  a2_div := H.a2_div
  b3_div i := dvd_mul_of_dvd_right (H.b3_div ⟨n, by omega⟩) _
  b4_div i := dvd_mul_of_dvd_right (H.b4_div ⟨n, by omega⟩) _
  b6_div i := dvd_mul_of_dvd_right (H.b6_div ⟨n, by omega⟩) _

include H in
/-- A nonunit uniformizer forces the original starting depth to be positive. -/
theorem ArithmeticAtlasCoefficients.start_pos (hπ : ¬ IsUnit π) : 0 < start := by
  by_contra h
  have hz : start = 0 := by omega
  have hd : π ∣ (1 : R) := by simpa [hz] using H.scale_div
  exact hπ (isUnit_of_dvd_one hd)

/-- The number of transitions in the extension retains every original retained label. -/
def startOneRetainedIndex (k : ℕ) (a : Fin k) : Fin (start - 1 + k) :=
  ⟨start - 1 + a.val, Nat.add_lt_add_left a.isLt _⟩

include hstart in
/-- The source smoothing at an old retained label keeps its original depth. -/
theorem startOneRetainedIndex_depth (k : ℕ) (a : Fin k) :
    1 + (startOneRetainedIndex (start := start) k a).val = start + a.val := by
  dsimp [startOneRetainedIndex]
  omega

include hstart in
/-- Extending any admissible stage stays inside the extended family. -/
theorem startOneStage_le (k : ℕ) (hk : k ≤ n) :
    start - 1 + k ≤ startOneLength (start := start) (n := n) := by
  unfold startOneLength
  omega

end FLT.Mazur.WeierstrassDividedDepth
