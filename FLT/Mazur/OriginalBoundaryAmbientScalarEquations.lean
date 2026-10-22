/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryTensorLift
public import FLT.Mazur.FiniteFreeRingQuotientComparison

/-!
# Boundary equations from a basis of the uncut original source

An affine closed immersion supplies the boundary surjection. The source
basis is over the full original invariant ring, and the complete frame is
on the uncut source. The boundary itself is allowed to be nonflat.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module TensorProduct
open scoped BigOperators
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} (J : A.IdealSheafData) [IsAffine A]
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom

/-- Affine boundary restriction is surjective on the entire original source ring. -/
theorem originalBoundaryMap_surjective :
    Function.Surjective (originalBoundaryMap (p := p) (q := q) J) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine J.subschemeι).2

variable {T I : Type} [CommRing T]
  [Algebra (invariants p.appTop.hom q.appTop.hom) T] [Fintype I] {d : ℕ}
  (basis : Basis (Fin d) (invariants p.appTop.hom q.appTop.hom) Γ(A, ⊤))
  (l : I → Γ(J.subscheme, ⊤) →+* T) (y : Γ(J.subscheme, ⊤) →+* T)
include basis

/-- The uncut source norm gives all full boundary equations on an arbitrary scalar test. -/
theorem originalBoundary_ambient_mixed_products_eq_zero
    (frame : (T ⊗[R] Γ(A, ⊤)) ≃ₐ[T] (I → T))
    (hy : ∀ r : invariants p.appTop.hom q.appTop.hom,
      y (J.subschemeι.appTop r.val) = algebraMap R T r)
    (hframe : ∀ (i : I) (z : Γ(A, ⊤)), frame ((1 : T) ⊗ₜ[R] z) i = l i (J.subschemeι.appTop z))
    (z : I → Γ(J.subscheme, ⊤)) : (∏ i, (l i (z i) - y (z i))) = 0 := by
  exact FiniteFreeRingQuotientComparison.mixed_products_eq_zero basis
    (originalBoundaryMap (p := p) (q := q) J).toRingHom
    (originalBoundaryMap_surjective (p := p) (q := q) J) l y frame hy hframe z

/-- The same source construction controls correction ideals without boundary flatness. -/
theorem originalBoundary_ambient_mixed_products_mem (K : Ideal T)
    (frame : ((T ⧸ K) ⊗[R] Γ(A, ⊤)) ≃ₐ[T ⧸ K] (I → T ⧸ K))
    (hy : ∀ r : invariants p.appTop.hom q.appTop.hom,
      y (J.subschemeι.appTop r.val) = algebraMap R T r)
    (hframe : ∀ (i : I) (z : Γ(A, ⊤)), frame ((1 : T ⧸ K) ⊗ₜ[R] z) i =
      Ideal.Quotient.mk K (l i (J.subschemeι.appTop z)))
    (z : I → Γ(J.subscheme, ⊤)) : (∏ i, (l i (z i) - y (z i))) ∈ K := by
  exact FiniteFreeRingQuotientComparison.mixed_products_mem basis
    (originalBoundaryMap (p := p) (q := q) J).toRingHom
    (originalBoundaryMap_surjective (p := p) (q := q) J) l y K frame hy hframe z

end FLT.Mazur.EquivalenceRelationOrderedFrames
