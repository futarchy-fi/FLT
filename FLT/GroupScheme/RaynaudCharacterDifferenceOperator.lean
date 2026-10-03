/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudUniversalCharacterConstant

/-!
# The character finite-difference operator on monomials

The operator lowers polynomial degree. Its top coefficient is the degree
when the character is induced by the field embedding used in the monomial.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R F : Type*} [CommRing R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)]

/-- The normalized finite difference as a linear endomorphism of functions. -/
def step (χ : Fˣ →* Rˣ) : Module.End R (F → R) where
  toFun f a := ⅟(Fintype.card Fˣ : R) * ∑ u : Fˣ,
    (↑(χ u)⁻¹ : R) * (f (a + u) - f a)
  map_add' f g := by
    ext a
    simp only [Pi.add_apply, add_sub_add_comm, mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    ext a
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, ← mul_sub,
      mul_left_comm, ← Finset.mul_sum]

/-- The explicit recursion is iteration of the bundled difference operator. -/
theorem iterate_eq_step_pow (χ : Fˣ →* Rˣ) (f : F → R) (n : ℕ) :
    iterate χ f n = (step χ ^ n) f := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, ← hn]
    rfl

/-- Coefficients of the image of a monomial under the difference operator. -/
def monomialCoefficient (χ : Fˣ →* Rˣ) (e : F →+* R) (m i : ℕ) : R :=
  ⅟(Fintype.card Fˣ : R) * ∑ u : Fˣ,
    (↑(χ u)⁻¹ : R) * (e u ^ (m - i) * (m.choose i : R))

/-- Taking one difference lowers the degree of every monomial. -/
theorem step_monomial (χ : Fˣ →* Rˣ) (e : F →+* R) (m : ℕ) :
    step χ (fun a ↦ e a ^ m) =
      ∑ i ∈ Finset.range m, monomialCoefficient χ e m i • (fun a ↦ e a ^ i) := by
  ext a
  have hb (u : Fˣ) : e (a + u) ^ m - e a ^ m =
      ∑ i ∈ Finset.range m, e a ^ i * e u ^ (m - i) * (m.choose i : R) := by
    rw [map_add, add_pow, Finset.sum_range_succ]
    simp
  change ⅟(Fintype.card Fˣ : R) * ∑ u : Fˣ,
    (↑(χ u)⁻¹ : R) * (e (a + u) ^ m - e a ^ m) = _
  simp_rw [hb, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, monomialCoefficient,
    mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-- For an embedding character the top coefficient is exactly the monomial degree. -/
theorem monomialCoefficient_top (χ : Fˣ →* Rˣ) (e : F →+* R)
    (he : ∀ u : Fˣ, (χ u : R) = e u) (n : ℕ) :
    monomialCoefficient χ e (n + 1) n = (n + 1 : ℕ) := by
  simp only [monomialCoefficient, Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right]
  simp_rw [← he, ← mul_assoc, Units.inv_mul, one_mul]
  simp [← Nat.cast_smul_eq_nsmul R]

end ThreeAdicPlan.CharacterAverage
