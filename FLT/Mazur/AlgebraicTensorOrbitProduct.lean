/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AlgebraicTensorCoefficientOrbit
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# A nonzero product controlling every algebraic coefficient conjugate

Multiply the finitely many distinct conjugates of a coefficient function.
On an integral algebraic fiber this product is nonzero. Any point avoiding
its zero locus avoids every conjugate function, including conjugates indexed
by an infinite automorphism group.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AlgebraicTensorCoefficientOrbit
open scoped TensorProduct
variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing A] [Algebra k A] [Algebra.IsAlgebraic k L]

/-- The product uses distinct orbit elements, not the possibly infinite automorphism group. -/
def orbitProduct (x : L ⊗[k] A) : L ⊗[k] A :=
  ∏ y ∈ (finite_orbit x).toFinset, y

/-- Integral geometric fibers keep the orbit product nonzero. -/
theorem orbitProduct_ne_zero [IsDomain (L ⊗[k] A)] (x : L ⊗[k] A) (hx : x ≠ 0) :
    orbitProduct x ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  obtain ⟨σ, rfl⟩ := (finite_orbit x).mem_toFinset.mp hy
  intro h
  exact hx ((action σ).injective (h.trans (map_zero _).symm))

/-- Nonvanishing of one product controls every conjugate at the same point. -/
theorem all_conjugates_ne_zero {F : Type*} [Field F]
    (p : L ⊗[k] A →+* F) (x : L ⊗[k] A) (hp : p (orbitProduct x) ≠ 0)
    (σ : L ≃ₐ[k] L) : p (action σ x) ≠ 0 := by
  classical
  have h : (∏ y ∈ (finite_orbit x).toFinset, p y) ≠ 0 := by
    simpa only [orbitProduct, map_prod] using hp
  exact (Finset.prod_ne_zero_iff.mp h) _ ((finite_orbit x).mem_toFinset.mpr ⟨σ, rfl⟩)

end FLT.Mazur.AlgebraicTensorCoefficientOrbit
