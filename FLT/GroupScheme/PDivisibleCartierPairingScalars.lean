/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierPairingBilinear

/-! # The original Tate root pairing is balanced over the p-adic integers -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- An actual p-adic scalar on the dual Tate vector acts by the finite residue exponent. -/
theorem cartierTatePairing_padic_smul_left (a : ℤ_[p])
    (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing (a • y) x n =
      X.cartierTatePairing y x n ^ (PadicInt.toZModPow n a).val := by
  let k := (PadicInt.toZModPow n a).val
  have he : X.cartierTateEval n (a • y) = X.cartierTateEval n (k • y) := by
    rw [map_smul, map_nsmul, X.cartierDual.padic_smul_points,
      ← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), Nat.cast_smul_eq_nsmul]
  have h := congrArg (fun f : X.tateSequences →+ Additive (AlgebraicClosure K)ˣ ↦ f x)
    ((X.cartierTatePairingHom n).map_nsmul k y)
  change X.cartierTatePairing (k • y) x n = X.cartierTatePairing y x n ^ k at h
  rw [← h]
  exact congrArg (fun z ↦ (X.level n).cartierPairing z (X.tateEval n x)) he

/-- An actual p-adic scalar on the original Tate vector acts by the same residue exponent. -/
theorem cartierTatePairing_padic_smul_right (a : ℤ_[p])
    (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing y (a • x) n =
      X.cartierTatePairing y x n ^ (PadicInt.toZModPow n a).val := by
  let k := (PadicInt.toZModPow n a).val
  have he : X.tateEval n (a • x) = X.tateEval n (k • x) := by
    change X.tateEvalLinear n (a • x) = X.tateEvalLinear n (k • x)
    rw [map_smul, map_nsmul, X.padic_smul_points,
      ← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), Nat.cast_smul_eq_nsmul]
  have h := (X.cartierTatePairingHom n y).map_nsmul k x
  change X.cartierTatePairing y (k • x) n = X.cartierTatePairing y x n ^ k at h
  rw [← h]
  exact congrArg (X.cartierTateLevelPairing n y) he

/-- The root pairing balances the original p-adic actions, level by level. -/
theorem cartierTatePairing_padic_balanced (a : ℤ_[p])
    (y : X.CartierTate) (x : X.tateSequences) (n : ℕ) :
    X.cartierTatePairing (a • y) x n = X.cartierTatePairing y (a • x) n := by
  rw [X.cartierTatePairing_padic_smul_left, X.cartierTatePairing_padic_smul_right]

end ThreeAdicPlan.PDivisibleSystem
