/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedInitialBoundary
public import FLT.Mazur.LaurentNearIdentityAutomorphism

/-!
# The full right parameter of the first retained node

At depth zero the scalar depth factor is one. The entire original root
correction defines an automorphism congruent to the identity in the base ideal.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "t" => parameter R π m
local notation "J" => ideal Q t
local notation "K" => Ideal.map (algebraMap Q L) J
local notation "a" => (Fin.mk 0 (Nat.zero_lt_succ j))
local notation "V" => arithmeticRetainedFullCorrection data H m (j + 1) hj a
local notation "F" => AlgHom.comp (leftLaurentMap t) (branchSwapMap t)
local notation "U" => retainedFixedRightUnit t V

/-- The actual depth-zero right coordinate differs from T only in the original base ideal. -/
theorem arithmeticInitialRightUnit_sub_mem : (U : L) - T 1 ∈ K := by
  let f := Ideal.Quotient.mk K
  have hv : Units.map (f.comp (F).toRingHom).toMonoidHom V = 1 := by
    unfold arithmeticRetainedFullCorrection
    refine retainedFactorCorrectionUnit_reduction (S := L ⧸ K)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ (f.comp (F).toRingHom) ?_
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change f (F (algebraMap Q _ x)) = 0
    rw [AlgHom.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
  have hh := congrArg Units.val hv
  change f (F (V : ChartRing t)) = 1 at hh
  apply Ideal.Quotient.eq.mp
  change f (T 1 * F (V : ChartRing t)) = f (T 1)
  rw [map_mul, hh]
  exact mul_one (f (T 1))

/-- The full original depth-zero right substitution has a constructed inverse. -/
def arithmeticInitialRightEquiv : L ≃ₐ[Q] L :=
  LaurentNearIdentityAutomorphism.equiv J (arithmeticParameterIdeal_nilpotent π m) U
    (arithmeticInitialRightUnit_sub_mem data H m j hj)

local notation "B" => arithmeticInitialRightEquiv data H m j hj

/-- Every Laurent function retains the exact coefficient-ideal congruence. -/
theorem arithmeticInitialRightEquiv_sub_mem (z : L) : B z - z ∈ K :=
  LaurentNearIdentityAutomorphism.eval_sub_mem J U
    (arithmeticInitialRightUnit_sub_mem data H m j hj) z

/-- The constructed inverse also differs from the identity only in that same ideal. -/
theorem arithmeticInitialRightEquiv_symm_sub_mem (z : L) : (B).symm z - z ∈ K :=
  LaurentNearIdentityAutomorphism.symm_sub_mem J (arithmeticParameterIdeal_nilpotent π m) U
    (arithmeticInitialRightUnit_sub_mem data H m j hj) z

/-- Its spectrum is exactly the right parameter already used by the original initial edge. -/
theorem arithmeticInitialRightEquiv_spec :
    (punctureSpecIso B).hom = arithmeticRetainedRightParameter data H m j hj a := by
  unfold arithmeticRetainedRightParameter
  simp only [retainedDepthScale, pow_zero, mul_one, retainedScaledCorrectionUnit,
    map_one, one_mul]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
