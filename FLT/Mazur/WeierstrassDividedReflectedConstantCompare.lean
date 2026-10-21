/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReflectedBranchData

/-!
# Compare the reflected constant with the deeper input coefficient

Cancel the original nonzero parameter power, using both actual divided
factorizations. At even terminal depth the reflected unit is precisely
the full deeper constant coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l) (hl : 2 * l ≤ m)

/-- The deeper constant has exactly the common residual scale times the reflected unit. -/
theorem reflectedBranchConstant_deeper_factor :
    e.b6 = π ^ (m - 2 * l) * reflectedBranchConstant D d hkl hl := by
  apply mul_left_cancel₀ (pow_ne_zero (2 * l) D.uniformizer_ne_zero)
  calc
    π ^ (2 * l) * e.b6 = W.a₆ := by
      simpa only [mul_comm 2 l, pow_mul] using e.factor6.symm
    _ = π ^ (2 * k) * d.b6 := by
      simpa only [mul_comm 2 k, pow_mul] using d.factor6
    _ = π ^ (2 * l) * (π ^ (m - 2 * l) * reflectedBranchConstant D d hkl hl) := by
      rw [reflectedBranchConstant_factor D d hkl hl, ← mul_assoc, ← pow_add,
        ← mul_assoc, ← pow_add]
      congr 2
      omega

/-- At an even terminal input the reflected unit is the original deeper constant. -/
theorem reflectedBranchConstant_terminal (hm : m = 2 * l) :
    reflectedBranchConstant D d hkl hl = e.b6 := by
  have h := reflectedBranchConstant_deeper_factor D d e hkl hl
  simpa only [hm, Nat.sub_self, pow_zero, one_mul] using h.symm

end FLT.Mazur.WeierstrassDividedDepth
