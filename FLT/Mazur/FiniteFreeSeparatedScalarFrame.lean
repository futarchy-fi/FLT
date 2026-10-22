/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeCoordinateFrame
public import FLT.Mazur.ScalarCoordinateKernelSeparation
public import FLT.Mazur.FiniteFreeRingQuotientComparison

/-!
# Complete scalar frames from whole-source bases and original separation

Base change transports a whole-source basis to the prescribed scalar test.
Original coefficient separation supplies comaximal coordinate kernels.
Chinese remainders and finite free injectivity construct the full frame,
which can then be used in the previously constructed scalar norm equation.
-/

@[expose] public noncomputable section
open Module TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteFreeSeparatedScalarFrame
open FiniteCoefficientDifference ScalarCoordinateKernelSeparation
variable {R A T I : Type*} [CommRing R] [CommRing A] [CommRing T]
  [Algebra R A] [Algebra R T] [Fintype I]
  (b : Basis I R A) (l : I → A →ₐ[R] T)
  (hl : Pairwise fun i j ↦ differenceIdeal (l i).toRingHom (l j).toRingHom = ⊤)

/-- A full source frame is constructed from a basis indexed by the separated coordinates. -/
def frame : (T ⊗[R] A) ≃ₐ[T] (I → T) :=
  FiniteFreeCoordinateFrame.frame (fun i ↦ coordinate (l i)) (b.baseChange T)
    (fun i j hij ↦ kernels_coprime (l i) (l j) (hl hij))

/-- The constructed frame retains the prescribed original source coordinate maps. -/
theorem frame_coefficient (a : A) (i : I) : frame b l hl (1 ⊗ₜ[R] a) i = l i a :=
  coordinate_coefficient (l i) a

variable {B : Type*} [CommRing B] {n : ℕ}

/-- Matching whole-source rank and separation kill every boundary equation. -/
theorem boundary_mixed_products_eq_zero (b : Basis (Fin n) R A)
    (π : A →+* B) (hπ : Function.Surjective π) (l : Fin n → B →+* T)
    (source : Fin n → A →ₐ[R] T) (hsource : ∀ i a, source i a = l i (π a))
    (hsep : Pairwise fun i j ↦ differenceIdeal (source i).toRingHom
      (source j).toRingHom = ⊤)
    (y : B →+* T) (hy : ∀ r, y (π (algebraMap R A r)) = algebraMap R T r)
    (z : Fin n → B) : (∏ i, (l i (z i) - y (z i))) = 0 := by
  apply FiniteFreeRingQuotientComparison.mixed_products_eq_zero b π hπ l y
    (frame b source hsep) hy _ z
  intro i a
  exact (frame_coefficient b source hsep a i).trans (hsource i a)


/-- Separation after a correction quotient controls all boundary equations in that ideal. -/
theorem boundary_mixed_products_mem (b : Basis (Fin n) R A)
    (π : A →+* B) (hπ : Function.Surjective π) (l : Fin n → B →+* T) (K : Ideal T)
    (source : Fin n → A →ₐ[R] T ⧸ K)
    (hsource : ∀ i a, source i a = Ideal.Quotient.mk K (l i (π a)))
    (hsep : Pairwise fun i j ↦ differenceIdeal (source i).toRingHom
      (source j).toRingHom = ⊤)
    (y : B →+* T) (hy : ∀ r, y (π (algebraMap R A r)) = algebraMap R T r)
    (z : Fin n → B) : (∏ i, (l i (z i) - y (z i))) ∈ K := by
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have h := boundary_mixed_products_eq_zero b π hπ
    (fun i ↦ (Ideal.Quotient.mk K).comp (l i)) source hsource hsep
    ((Ideal.Quotient.mk K).comp y) (fun r ↦ congrArg (Ideal.Quotient.mk K) (hy r)) z
  simpa only [map_prod, map_sub, RingHom.comp_apply] using h

end FLT.Mazur.FiniteFreeSeparatedScalarFrame
