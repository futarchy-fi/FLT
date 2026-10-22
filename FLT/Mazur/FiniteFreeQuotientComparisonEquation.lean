/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeSplitComparisonEquation

/-!
# Full mixed equations descend from an uncut finite free source

The boundary algebra is only a quotient of the finite free source. It need
not be flat over the original scalars. Lift the finitely many selected
coefficients to the uncut source and use its complete scalar frame.
-/

@[expose] public noncomputable section
open Module TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteFreeQuotientComparisonEquation
open PolynomialTensorSplitFrame FiniteCoefficientDifference
set_option backward.isDefEq.respectTransparency false
variable {R A B T I : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T] [Fintype I] {d : ℕ}
  (b : Basis (Fin d) R A) (π : A →ₐ[R] B) (hπ : Function.Surjective π)
  (e : (T ⊗[R] A) ≃ₐ[T] (I → T)) (l : I → B →+* T) (y : B →ₐ[R] T)
  (he : ∀ i a, e (1 ⊗ₜ[R] a) i = l i (π a))
include b hπ he

/-- A whole uncut scalar frame kills every mixed equation on a possibly nonflat quotient. -/
theorem mixed_products_eq_zero (z : I → B) : (∏ i, (l i (z i) - y (z i))) = 0 := by
  choose a ha using fun i ↦ hπ (z i)
  have h := FiniteFreeSplitComparisonEquation.mixed_products_eq_zero b e (y.comp π) a
  change (∏ i, (e (1 ⊗ₜ[R] a i) i - y (π (a i)))) = 0 at h
  simpa only [he, ha] using h

/-- The exact full product of boundary equality ideals vanishes after quotient transport. -/
theorem product_differenceIdeal_eq_bot :
    (∏ i, differenceIdeal (l i) y.toRingHom) = ⊥ := by
  rw [product_differenceIdeal_eq_bot_iff]
  exact mixed_products_eq_zero b π hπ e l y he

end FLT.Mazur.FiniteFreeQuotientComparisonEquation
