/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MarkedIntegerModel

/-!
# Integer models of units and multiplicative identities

Finitely many units descend together with finitely many identities of the
form `uᵢ uⱼ = uₖ`. Both the units and their inverses are constructed in the
model. This handles the equations in local line-bundle transition data;
compatibility with overlap maps and sheaf gluing remain separate steps.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v w

/-- Descend a finite family of units and prescribed multiplicative identities. -/
theorem exists_integer_model_units {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FinitePresentation A B]
    {κ : Type v} [Finite κ] {τ : Type w} [Finite τ]
    (x : κ → Bˣ) (a b c : τ → κ) (h : ∀ j, x (a j) * x (b j) = x (c j))
    (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        Algebra.FinitePresentation A₀ B₀ ∧
          ∃ (e : A ⊗[A₀] B₀ ≃ₐ[A] B) (x₀ : κ → B₀ˣ),
            (∀ k, e (1 ⊗ₜ (x₀ k : B₀)) = (x k : B)) ∧
              ∀ j, x₀ (a j) * x₀ (b j) = x₀ (c j) := by
  let y : κ × Bool → B := fun k ↦ if k.2 then ↑(x k.1)⁻¹ else ↑(x k.1)
  let r : κ ⊕ τ → MvPolynomial (κ × Bool) ℤ := Sum.elim
    (fun k ↦ X (k, false) * X (k, true) - 1)
    (fun j ↦ X (a j, false) * X (b j, false) - X (c j, false))
  have hr (j) : aeval y (r j) = 0 := by
    cases j with
    | inl k => simp [r, y]
    | inr j => simpa [r, y, sub_eq_zero] using congrArg (fun z : Bˣ ↦ (z : B)) (h j)
  obtain ⟨A₀, hA₀, hs₀, B₀, _, _, hB₀, e, y₀, hy₀, hr₀⟩ :=
    exists_integer_model_marked (A := A) y r hr s hs
  have hinv (k) : y₀ (k, false) * y₀ (k, true) = 1 := by
    simpa [r, sub_eq_zero] using hr₀ (.inl k)
  let x₀ : κ → B₀ˣ := fun k ↦
    ⟨y₀ (k, false), y₀ (k, true), hinv k, (mul_comm _ _).trans (hinv k)⟩
  refine ⟨A₀, hA₀, hs₀, B₀, inferInstance, inferInstance, hB₀, e, x₀, ?_, ?_⟩
  · intro k
    simpa only [x₀, y, Bool.false_eq_true, ↓reduceIte] using hy₀ (k, false)
  · intro j
    apply Units.ext
    simpa [x₀, r, sub_eq_zero] using hr₀ (.inr j)

end FLT.Mazur.Approximation
