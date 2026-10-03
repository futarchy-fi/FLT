/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFiniteValuation
public import FLT.GroupScheme.RaynaudScalingValuation

/-!
# Cyclic integral scalings are units below the ramification bound

Complementary parameter products supply all nonvanishing and valuation
bounds. The existing maximum-valuation argument then kills every scaling
valuation, proving invertibility of the actual coefficients.
-/

@[expose] public noncomputable section
namespace RaynaudParameters

variable {R ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite ι]

/-- Actual complementary products and cyclic equations force all nonzero scalings to be units. -/
theorem isUnit_cyclic_scalings (p : ℕ) (hp : 1 ≤ p) (hpR : (p : R) ≠ 0)
    (he : order (p : R) < p - 1) (next : ι → ι) (a b c : ι → R)
    (ha : ∀ i, ∃ (d : R) (u : Rˣ), a i * d = (p : R) * u)
    (hb : ∀ i, ∃ (d : R) (u : Rˣ), b i * d = (p : R) * u)
    (hc : ∀ i, c i ≠ 0) (hrel : ∀ i, c i ^ p * a i = b i * c (next i)) :
    ∀ i, IsUnit (c i) := by
  have hav (i : ι) : a i ≠ 0 ∧ order (a i) ≤ order (p : R) := by
    obtain ⟨d, u, h⟩ := ha i
    exact order_le_of_product hpR u h
  have hbv (i : ι) : b i ≠ 0 ∧ order (b i) ≤ order (p : R) := by
    obtain ⟨d, u, h⟩ := hb i
    exact order_le_of_product hpR u h
  have hval (i : ι) :
      (order (b i) : ℤ) + order (c (next i)) = p * (order (c i) : ℤ) + order (a i) := by
    have h := congrArg order (hrel i).symm
    rw [order_mul (hbv i).1 (hc _), order_mul (pow_ne_zero _ (hc i)) (hav i).1,
      order_pow (hc i)] at h
    exact_mod_cast h
  have hz := scaling_eq_zero_of_small_ramification next
    (fun i ↦ (order (a i) : ℤ)) (fun i ↦ (order (b i) : ℤ))
    (fun i ↦ (order (c i) : ℤ)) hp he
    (fun i ↦ Int.natCast_nonneg _) (fun i ↦ by exact_mod_cast (hbv i).2)
    (fun i ↦ Int.natCast_nonneg _) hval
  intro i
  apply (order_eq_zero_iff (hc i)).mp
  exact_mod_cast hz i

end RaynaudParameters
