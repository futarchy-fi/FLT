/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueDepth
public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# The actual linear coefficient bound at the next divided depth

Linear coefficients only require k at most the node depth. The quadratic
bound used for the divided constant is unnecessary for the two next-line coefficients.
-/

@[expose] public section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
include D

/-- Both divided linear coefficients vanish under their precise linear depth bound. -/
theorem dividedLinear_residue_zero {k : ℕ} (hk : k ≤ depth) (d : Data W π k) :
    residue R d.b3 = 0 ∧ residue R d.b4 = 0 := by
  have hm : maximalIdeal R ^ (depth + 1) ≤ maximalIdeal R ^ (k + 1) :=
    Ideal.pow_le_pow_right (by omega)
  constructor
  · apply (residue_eq_zero_iff _).mpr
    simpa only [pow_one] using WeierstrassDilatation.divided_mem_power D k 1
      (d.factor3 ▸ hm D.a₃_mem)
  · apply (residue_eq_zero_iff _).mpr
    simpa only [pow_one] using WeierstrassDilatation.divided_mem_power D k 1
      (d.factor4 ▸ hm D.a₄_mem)

/-- A conic strictly before the middle depth supplies both next-line residue coefficients. -/
theorem dividedLinear_next_residue_zero {k : ℕ} (hk : 2 * (k + 1) < depth)
    (d : Data W π (k + 2)) : residue R d.b3 = 0 ∧ residue R d.b4 = 0 :=
  dividedLinear_residue_zero D (by omega) d

/-- The actual indexed next retained line needs no separate linear-coefficient hypotheses. -/
theorem dividedLinear_adjacent_residue_zero {start n j : ℕ}
    (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hj : j + 2 ≤ n)
    (hk : 2 * (start + j + 1) < depth) :
    residue R (data ⟨j + 2, by omega⟩).b3 = 0 ∧
      residue R (data ⟨j + 2, by omega⟩).b4 = 0 := by
  apply dividedLinear_residue_zero D (d := data ⟨j + 2, by omega⟩)
  change start + (j + 2) ≤ depth
  omega

end FLT.Mazur.WeierstrassDividedDepth
