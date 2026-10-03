/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTorsionFiltration
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Algebra.Module.ZMod

/-!
# Prime-field point actions and compatible invariant subspaces

The actual additive Galois action is automatically prime-field linear.
If each Galois element acts like an element of another group, every subspace
invariant under that group's representation is Galois invariant.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (X : FF R K) (p : ℕ) [Module (ZMod p) X.Points]

/-- The actual point action, expressed as a prime-field-linear representation. -/
def FF.primeRepresentation :
    Representation (ZMod p) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points where
  toFun σ := (DistribMulAction.toAddMonoidEnd _ X.Points σ).toZModLinearMap p
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_smul]

/-- Passing to the linear representation leaves the actual point action unchanged. -/
@[simp] theorem FF.primeRepresentation_apply (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : X.Points) : X.primeRepresentation p σ x = σ • x := rfl

variable {G : Type*} [Monoid G] (ρ : Representation (ZMod p) G X.Points)
  (h : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∃ g : G,
    ∀ x : X.Points, σ • x = ρ g x)

/-- An invariant subspace for the agreeing action is invariant for the actual Galois action. -/
def FF.agreedSubrepresentation (W : Subrepresentation ρ) :
    Subrepresentation (X.primeRepresentation p) :=
  ⟨W.toSubmodule, fun σ x hx ↦ by
    obtain ⟨g, hg⟩ := h σ
    change σ • x ∈ W
    rw [hg]
    exact W.apply_mem_toSubmodule g hx⟩

end ThreeAdicPlan
