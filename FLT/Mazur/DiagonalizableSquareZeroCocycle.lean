/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableSquareZeroCoefficients

/-!
# Correcting multiplicative defects over a square-zero base ideal

A full multiplicative two-cocycle congruent to one has an explicit correcting
unit. The proof uses integral character contraction and retains the exact
coordinate-ring equation. It applies to roots of unity even when their order
vanishes in the coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable {R G : Type*} [CommRing R] [AddCommMonoid G]
  (I : Ideal R) (hI : I ^ 2 = ⊥)
  (p : AddMonoidAlgebra R (G × G)) (hp : InCoefficients I p)

include hI hp in
/-- The original multiplicative equation implies the complete additive defect equation. -/
theorem additive_of_multiplicative
    (hc : frontMap R G (1 + p) * leftProductMap R G (1 + p) =
      backMap R G (1 + p) * rightProductMap R G (1 + p)) :
    frontMap R G p + leftProductMap R G p =
      backMap R G p + rightProductMap R G p := by
  have hl : frontMap R G p * leftProductMap R G p = 0 :=
    (hp.mapDomain I _).mul_eq_zero I hI (hp.mapDomain I _)
  have hr : backMap R G p * rightProductMap R G p = 0 :=
    (hp.mapDomain I _).mul_eq_zero I hI (hp.mapDomain I _)
  simp only [map_add, map_one, add_mul, mul_add, one_mul, mul_one, hl, hr, add_zero] at hc
  have h : 1 + (frontMap R G p + leftProductMap R G p) =
      1 + (backMap R G p + rightProductMap R G p) := by
    calc
      _ = 1 + frontMap R G p + leftProductMap R G p := by abel
      _ = 1 + backMap R G p + rightProductMap R G p := hc
      _ = _ := by abel
  exact add_left_cancel h

/-- The coefficient contraction supplies a unit reducing to one. -/
def correctionUnit : (AddMonoidAlgebra R G)ˣ :=
  Units.mkOfMulEqOne (1 + correction R G p) (1 - correction R G p) (by
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, correction_sq_zero I hI hp]
    abel)

/-- The actual correcting unit retains the full integral correction. -/
theorem correctionUnit_val : (correctionUnit I hI p hp).val = 1 + correction R G p := rfl

/-- Its inverse is an exact formula, not a truncated infinite series. -/
theorem correctionUnit_inv_val :
    ((correctionUnit I hI p hp)⁻¹).val = 1 - correction R G p := rfl

/-- The constructed unit preserves the prescribed reduction on the entire original base. -/
theorem correctionUnit_reduction :
    AddMonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I)
      (correctionUnit I hI p hp).val = 1 := by
  rw [correctionUnit_val, map_add, map_one,
    (inCoefficients_iff_reduction I _).mp (hp.correction I), add_zero]

/-- The correcting unit kills the original full multiplicative cocycle. -/
theorem correctionUnit_equation
    (hc : frontMap R G (1 + p) * leftProductMap R G (1 + p) =
      backMap R G (1 + p) * rightProductMap R G (1 + p)) :
    (1 + p) * diagonalMap R G (correctionUnit I hI p hp).val =
      firstMap R G (correctionUnit I hI p hp).val *
        secondMap R G (correctionUnit I hI p hp).val := by
  have hq := hp.correction I
  have hl : p * diagonalMap R G (correction R G p) = 0 :=
    hp.mul_eq_zero I hI (hq.mapDomain I _)
  have hr : firstMap R G (correction R G p) * secondMap R G (correction R G p) = 0 :=
    (hq.mapDomain I _).mul_eq_zero I hI (hq.mapDomain I _)
  have he := algebra_cocycle_eq R G p (additive_of_multiplicative I hI p hp hc)
  simp only [correctionUnit_val, map_add, map_one, add_mul, mul_add, one_mul,
    mul_one, hl, hr, add_zero]
  nth_rw 1 [he]
  abel

end FLT.Mazur.DiagonalizableCobar
