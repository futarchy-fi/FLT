/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeSplitComparisonEquation

/-!
# Mixed equations on ring quotients of finite free scalar sources

Only the uncut source and the test carry scalar algebra structures. The
boundary restriction is a surjective ring map, so the boundary needs no
chosen scalar action. This form also separates scalar compatibility from
large geometric expressions when applying the constructed norm.
-/

@[expose] public noncomputable section
open Module TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteFreeRingQuotientComparison
variable {R A B T I : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R T] [Fintype I] {d : ℕ}
  (b : Basis (Fin d) R A) (π : A →+* B) (hπ : Function.Surjective π)
  (l : I → B →+* T) (y : B →+* T)

include hπ

/-- Surjective restriction transports mixed vanishing without a boundary scalar action. -/
theorem mixed_products_of_source
    (h : ∀ z : I → A, (∏ i, (l i (π (z i)) - y (π (z i)))) = 0)
    (z : I → B) : (∏ i, (l i (z i) - y (z i))) = 0 := by
  choose a ha using fun i ↦ hπ (z i)
  simpa only [ha] using h a

include b

/-- The constructed source norm kills every equation of a surjective ring quotient. -/
theorem mixed_products_eq_zero
    (e : (T ⊗[R] A) ≃ₐ[T] (I → T))
    (hy : ∀ r, y (π (algebraMap R A r)) = algebraMap R T r)
    (he : ∀ i a, e (1 ⊗ₜ[R] a) i = l i (π a))
    (z : I → B) : (∏ i, (l i (z i) - y (z i))) = 0 := by
  let yA : A →ₐ[R] T := ⟨y.comp π, hy⟩
  apply mixed_products_of_source π hπ l y _ z
  intro a
  have h := FiniteFreeSplitComparisonEquation.mixed_products_eq_zero b e yA a
  change (∏ i, (e (1 ⊗ₜ[R] a i) i - y (π (a i)))) = 0 at h
  simpa only [he] using h

/-- A frame over a correction quotient puts every mixed equation in that ideal. -/
theorem mixed_products_mem (K : Ideal T)
    (e : ((T ⧸ K) ⊗[R] A) ≃ₐ[T ⧸ K] (I → T ⧸ K))
    (hy : ∀ r, y (π (algebraMap R A r)) = algebraMap R T r)
    (he : ∀ i a, e (1 ⊗ₜ[R] a) i = Ideal.Quotient.mk K (l i (π a)))
    (z : I → B) : (∏ i, (l i (z i) - y (z i))) ∈ K := by
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have h := mixed_products_eq_zero b π hπ
    (fun i ↦ (Ideal.Quotient.mk K).comp (l i)) ((Ideal.Quotient.mk K).comp y) e
    (fun r ↦ congrArg (Ideal.Quotient.mk K) (hy r)) he z
  simpa only [map_prod, map_sub, RingHom.comp_apply] using h

end FLT.Mazur.FiniteFreeRingQuotientComparison
