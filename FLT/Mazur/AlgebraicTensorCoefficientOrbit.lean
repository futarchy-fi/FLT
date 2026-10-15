/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Finite orbits of algebraic tensor coefficients

An individual function on an affine algebra after algebraic scalar extension
has a finite orbit under the entire coefficient automorphism group. Neither
the extension nor its automorphism group is required to be finite.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AlgebraicTensorCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
  [CommRing A] [Algebra k A]

/-- Change only the algebraic scalar factor, retaining the original affine algebra. -/
def action (σ : L ≃ₐ[k] L) : L ⊗[k] A ≃ₐ[k] L ⊗[k] A :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[k] A)

/-- The action fixes the original factor of a pure tensor. -/
@[simp]
theorem action_tmul (σ : L ≃ₐ[k] L) (l : L) (a : A) :
    action σ (l ⊗ₜ[k] a) = σ l ⊗ₜ[k] a := rfl

variable [Algebra.IsAlgebraic k L]

/-- An algebraic scalar has finitely many conjugates, even in an infinite extension. -/
theorem finite_scalar_orbit (l : L) : (Set.range (fun σ : L ≃ₐ[k] L ↦ σ l)).Finite := by
  have hl : IsIntegral k l := (Algebra.IsAlgebraic.isAlgebraic l).isIntegral
  have hn : (minpoly k l).map (algebraMap k L) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hl)
  apply (Polynomial.finite_setOfPred_isRoot hn).subset
  rintro _ ⟨σ, rfl⟩
  simpa only [Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_map,
    ← Polynomial.aeval_def, AlgEquiv.toAlgHom_apply] using minpoly.aeval_algHom k σ.toAlgHom l

/-- Every individual algebraic-coefficient function has finite full automorphism orbit. -/
theorem finite_orbit (x : L ⊗[k] A) :
    (Set.range (fun σ : L ≃ₐ[k] L ↦ action σ x)).Finite := by
  induction x using TensorProduct.inductionOn with
  | tmul l a =>
    apply ((finite_scalar_orbit (k := k) l).image (fun z ↦ z ⊗ₜ[k] a)).subset
    rintro _ ⟨σ, rfl⟩
    exact ⟨σ l, ⟨σ, rfl⟩, rfl⟩
  | add x y hx hy =>
    apply (hx.add hy).subset
    rintro _ ⟨σ, rfl⟩
    exact ⟨action σ x, ⟨σ, rfl⟩, action σ y, ⟨σ, rfl⟩, (map_add _ _ _).symm⟩

end FLT.Mazur.AlgebraicTensorCoefficientOrbit
