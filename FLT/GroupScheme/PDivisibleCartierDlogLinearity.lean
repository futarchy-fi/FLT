/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierDlogAdditivity
public import FLT.GroupScheme.PadicTorsionScalarContinuity

/-! # P-adic linearity of the actual integral Tate differential -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K S : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  [CommRing S] [Algebra R S] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Every actual finite coefficient tensor remains killed by its original p-power. -/
theorem cotangentTensor_pow_smul_eq_zero (n : ℕ) (v : X.LevelCotangent n ⊗[R] S) :
    p ^ n • v = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul x s =>
    rw [TensorProduct.smul_tmul', X.cotangent_pow_smul_eq_zero, TensorProduct.zero_tmul]
  | add v w hv hw => rw [smul_add, hv, hw, add_zero]

/-- Finite residue scalars act on the actual finite Tate differential through the original base. -/
theorem cartierTateDlogAt_padic_smul (e : R ≃+* ℤ_[p])
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S)
    (n : ℕ) (a : ℤ_[p]) (y : X.CartierTate) :
    X.cartierTateDlogAt q n (a • y) = e.symm a • X.cartierTateDlogAt q n y := by
  let k := (PadicInt.toZModPow n a).val
  have he : X.cartierTateEval n (a • y) = X.cartierTateEval n (k • y) := by
    rw [map_smul, map_nsmul, X.cartierDual.padic_smul_points,
      ← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), Nat.cast_smul_eq_nsmul]
  have hd : X.cartierTateDlogAt q n (a • y) = X.cartierTateDlogAt q n (k • y) :=
    congrArg (fun z ↦ (X.level n).cartierDlog
      (q.comp ((X.level n).cartierDual.integralPointCoordinate z))) he
  have hs := torsion_smul_eq_of_padic_residue e n
    (X.cotangentTensor_pow_smul_eq_zero (S := S) n)
    (a := a) (b := (k : ℤ_[p])) (by simp [k]) (X.cartierTateDlogAt q n y)
  rw [hd]
  change X.cartierTateDlogAtHom q n (k • y) = _
  rw [map_nsmul, hs, map_natCast, Nat.cast_smul_eq_nsmul]
  rfl

/-- The original coherent integral dlog is p-adic linear under the specified base identification. -/
def cartierTateDlogLinear (e : R ≃+* ℤ_[p])
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) :
    X.CartierTate →ₛₗ[e.symm.toRingHom] X.CartierCotangentSequences (S := S) where
  __ := X.cartierTateDlogHom q
  map_smul' a y := by
    apply Subtype.ext
    funext n
    exact X.cartierTateDlogAt_padic_smul e q n a y

variable [∀ n, Finite (X.LevelCotangent n)]

/-- The same actual Tate map is p-adic linear in the integral completed coefficient tensor. -/
def cartierTateCompletedDlogLinear (e : R ≃+* ℤ_[p])
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) :
    X.CartierTate →ₛₗ[e.symm.toRingHom] X.CompletedCotangentTensor (S := S) :=
  X.cotangentTensorCompletionEquiv.symm.toLinearMap.comp (X.cartierTateDlogLinear e q)

/-- The linear map is exactly the completed original Cartier differential. -/
theorem cartierTateCompletedDlogLinear_apply (e : R ≃+* ℤ_[p])
    (q : integralClosure R (AlgebraicClosure K) →ₐ[R] S) (y : X.CartierTate) :
    X.cartierTateCompletedDlogLinear e q y = X.cartierTateCompletedDlog q y := rfl

end ThreeAdicPlan.PDivisibleSystem
