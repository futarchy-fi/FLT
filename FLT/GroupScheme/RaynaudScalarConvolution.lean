/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudReducedScalarAverage

/-!
# Iterated character averages and scalar convolution

Iterated finite differences encode the expansion of convolution powers of
the reduced character average. The recursion uses only field addition and
character values; linear maps commute with it.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open WithConv
namespace CharacterAverage

variable {R F V W : Type*} [CommRing R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The n-fold normalized character-weighted finite difference. -/
def iterate (χ : Fˣ →* Rˣ) (f : F → V) : ℕ → F → V
  | 0, a => f a
  | n + 1, a => ⅟(Fintype.card Fˣ : R) • ∑ u : Fˣ,
      (↑(χ u)⁻¹ : R) • (iterate χ f n (a + u) - iterate χ f n a)

/-- Every linear map commutes with the finite-difference expansion. -/
theorem map_iterate (χ : Fˣ →* Rˣ) (f : F → V) (g : V →ₗ[R] W) (n : ℕ) (a : F) :
    g (iterate χ f n a) = iterate χ (fun b ↦ g (f b)) n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n hn => simp only [iterate, map_smul, map_sum, map_sub, hn]

variable {A : Type*} [Ring A] [Algebra R A]

/-- Finite differences of scalar maps are powers of their reduced character average. -/
theorem iterate_eq_pow_mul (χ : Fˣ →* Rˣ) (s : F → A)
    (hadd : ∀ a b, s (a + b) = s a * s b) (n : ℕ) (a : F) :
    iterate χ s n a =
      s a * (⅟(Fintype.card Fˣ : R) • ∑ u : Fˣ, (↑(χ u)⁻¹ : R) • (s u - 1)) ^ n := by
  induction n generalizing a with
  | zero => simp [iterate]
  | succ n hn =>
    simp only [iterate, hn, hadd, pow_succ', mul_smul_comm, Finset.mul_sum,
      Finset.sum_mul, smul_mul_assoc, mul_sub, sub_mul, one_mul, mul_assoc]

end CharacterAverage

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K)
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))

include hadd

omit [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] in
/-- The integral scalar addition law is multiplication in the convolution algebra. -/
theorem FF.scalar_add_conv (a b : F) :
    toConv (lift (a + b)).toLinearMap =
      toConv (lift a).toLinearMap * toConv (lift b).toLinearMap := by
  rw [hadd]
  rfl

include h0 in
/-- Expand powers of the actual extended projector using only scalar addition. -/
theorem FF.characterProjector_convPow (χ : Fˣ →* Rˣ) (n : ℕ) :
    toConv (X.coordinateCharacterProjector lift h1 hmul χ) ^ n =
      CharacterAverage.iterate χ (fun a ↦ toConv (lift a).toLinearMap) n 0 := by
  rw [CharacterAverage.iterate_eq_pow_mul χ _ (X.scalar_add_conv lift hadd),
    X.scalar_zero_conv lift h0, one_mul,
    X.coordinateCharacterProjector_conv_average lift h0 h1 hmul]

end ThreeAdicPlan
