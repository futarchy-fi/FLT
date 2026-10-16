/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingComplementaryCoefficients

/-!
# Exact simultaneous extension of two Laurent boundary values

Compatibility is expressed in the original coefficients with the full powers
of the smoothing parameter. Complementary polynomial lifts construct the
unique node element; no invertibility or reduced-base assumption is used.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R] (t : R)

/-- The exact coefficient equations for a pair of full Laurent restrictions. -/
def LaurentCompatible (p q : R[T;T⁻¹]) : Prop :=
  (∀ k : ℕ, q.coeff k = t ^ k * p.coeff k) ∧
    ∀ k : ℕ, p.coeff (-(k : ℤ)) = t ^ k * q.coeff (-(k : ℤ))

/-- Construct an element using every outgoing nonnegative and incoming negative coefficient. -/
def pairedLaurentLift (p q : R[T;T⁻¹]) : ChartRing t :=
  outgoingPolynomialLift t p + incomingPolynomialLift t q

/-- Its nonnegative outgoing coefficients are the specified ones without any division. -/
theorem pairedLaurentLift_nonnegative (p q : R[T;T⁻¹]) (k : ℕ) :
    (leftLaurentMap t (pairedLaurentLift t p q)).coeff k = p.coeff k := by
  simp only [pairedLaurentLift, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    outgoingPolynomialLift_left_coeff, Nat.cast_nonneg, ite_true,
    incomingPolynomialLift_left_nonnegative t q k (Nat.cast_nonneg k), add_zero]

/-- Its strictly negative incoming coefficients are the specified ones. -/
theorem pairedLaurentLift_negative (p q : R[T;T⁻¹]) (k : ℤ) (hk : k < 0) :
    (precedingLaurentMap R t (pairedLaurentLift t p q)).coeff k = q.coeff k := by
  simp only [pairedLaurentLift, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    outgoingPolynomialLift_preceding_negative t p k hk,
    incomingPolynomialLift_preceding_coeff, ite_eq_left hk, zero_add]

/-- Compatibility recovers every outgoing coefficient, including the full negative tail. -/
theorem pairedLaurentLift_left (p q : R[T;T⁻¹]) (h : LaurentCompatible t p q) :
    leftLaurentMap t (pairedLaurentLift t p q) = p := by
  ext k
  by_cases hk : 0 ≤ k
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact pairedLaurentLift_nonnegative t p q k
  · have hn : k < 0 := by omega
    obtain ⟨l, hl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -k by omega)
    have he : k = -(l : ℤ) := by omega
    rw [he, branch_coefficient_nonpos,
      pairedLaurentLift_negative t p q _ (by omega), ← h.2 l]

/-- Compatibility also recovers the entire incoming Laurent value, including its constant. -/
theorem pairedLaurentLift_preceding (p q : R[T;T⁻¹]) (h : LaurentCompatible t p q) :
    precedingLaurentMap R t (pairedLaurentLift t p q) = q := by
  ext k
  by_cases hk : 0 ≤ k
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [branch_coefficient_nonneg, pairedLaurentLift_nonnegative, ← h.1 k]
  · exact pairedLaurentLift_negative t p q k (by omega)

/-- Every actual element satisfies precisely those two families of coefficient equations. -/
theorem laurentCompatible_restrictions (z : ChartRing t) :
    LaurentCompatible t (leftLaurentMap t z) (precedingLaurentMap R t z) :=
  ⟨branch_coefficient_nonneg t z, branch_coefficient_nonpos t z⟩

/-- The explicit extension recovers the original element when given its actual boundaries. -/
theorem pairedLaurentLift_restrictions (z : ChartRing t) :
    pairedLaurentLift t (leftLaurentMap t z) (precedingLaurentMap R t z) = z :=
  (laurent_reconstruction t z).symm

/-- The coefficient criterion is necessary and sufficient for one unique full-node extension. -/
theorem existsUnique_laurent_extension_iff (p q : R[T;T⁻¹]) :
    (∃! z : ChartRing t, leftLaurentMap t z = p ∧ precedingLaurentMap R t z = q) ↔
      LaurentCompatible t p q := by
  constructor
  · rintro ⟨z, ⟨rfl, rfl⟩, _⟩
    exact laurentCompatible_restrictions t z
  · intro h
    refine ⟨pairedLaurentLift t p q,
      ⟨pairedLaurentLift_left t p q h, pairedLaurentLift_preceding t p q h⟩, ?_⟩
    intro z hz
    rw [← hz.1, ← hz.2, pairedLaurentLift_restrictions]

/-- Equality on both original Laurent branches detects the whole node element. -/
theorem pairedLaurent_ext (z w : ChartRing t)
    (hl : leftLaurentMap t z = leftLaurentMap t w)
    (hr : precedingLaurentMap R t z = precedingLaurentMap R t w) : z = w := by
  rw [← pairedLaurentLift_restrictions t z, hl, hr, pairedLaurentLift_restrictions]

end FLT.Mazur.PolygonSmoothing
