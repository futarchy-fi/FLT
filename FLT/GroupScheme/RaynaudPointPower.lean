/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudEvaluatedCycle
public import FLT.GroupScheme.RaynaudValuationDigits

/-!
# Binary-weight root equations for actual finite-flat points

The coefficients and their digits are derived from the actual presentation.
For a two-cycle the first coordinate has exponent p*a+b, fixing the
orientation needed when comparing with Frobenius-conjugate characters.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)

include h0 hadd in
/-- A one-cycle point coordinate has a binary power of p times a unit as its root equation. -/
theorem FF.fundamentalValue_one_binary (hp : Irreducible (p : R))
    (hr : Fintype.card F = p ^ (1 : ℕ)) (x : X.Points) (hx : x ≠ 0) :
    ∃ (d : ℕ) (u : Rˣ), d ≤ 1 ∧
      X.fundamentalValue lift h1 hmul p hdim hlift e 0 x ^ (p - 1) =
        algebraMap R (AlgebraicClosure K) ((p : R) ^ d * u) := by
  obtain ⟨d, u, hd, hu⟩ := X.fundamentalCoefficient_eq_prime_pow_mul_unit
    lift h0 h1 hmul hadd p hdim hlift e 1 hr hp 0
  exact ⟨d, u, hd, (X.fundamentalValue_one lift h1 hmul p hdim hlift e hr x hx).trans
    (congrArg (algebraMap R (AlgebraicClosure K)) hu)⟩

include h0 hadd in
/-- A two-cycle point coordinate has its actual Frobenius-weighted binary root equation. -/
theorem FF.fundamentalValue_two_binary (hp : Irreducible (p : R))
    (hr : Fintype.card F = p ^ (2 : ℕ)) (x : X.Points) (hx : x ≠ 0) :
    ∃ (a b : ℕ) (u : Rˣ), a ≤ 1 ∧ b ≤ 1 ∧
      X.fundamentalValue lift h1 hmul p hdim hlift e 0 x ^ (p * p - 1) =
        algebraMap R (AlgebraicClosure K) ((p : R) ^ (p * a + b) * u) := by
  obtain ⟨a, u, ha, hu⟩ := X.fundamentalCoefficient_eq_prime_pow_mul_unit
    lift h0 h1 hmul hadd p hdim hlift e 2 hr hp 0
  obtain ⟨b, v, hb, hv⟩ := X.fundamentalCoefficient_eq_prime_pow_mul_unit
    lift h0 h1 hmul hadd p hdim hlift e 2 hr hp 1
  refine ⟨a, b, u ^ p * v, ha, hb, ?_⟩
  rw [X.fundamentalValue_two lift h1 hmul p hdim hlift e hr x hx, hu, hv]
  congr 1
  change ((p : R) ^ a * (u : R)) ^ p * ((p : R) ^ b * (v : R)) =
    (p : R) ^ (p * a + b) * ((u : R) ^ p * (v : R))
  rw [mul_pow, ← pow_mul, Nat.mul_comm a p, pow_add]
  ring

end ThreeAdicPlan
