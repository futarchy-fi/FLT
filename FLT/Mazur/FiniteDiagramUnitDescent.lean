/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntegerModelElementRelations
public import FLT.Mazur.FiniteIntegerModelUnits
public import FLT.Mazur.PrincipalChartIntegerDescent
public import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Compatible units and multiplicative equations in a finite diagram

Unit families descend along fixed model arrows, together with their
restriction compatibility and prescribed multiplicative equations. The
arrows are transported from the initial stage, so previously established
diagram identities remain available. This is algebraic transition data;
the associated invertible sheaf still requires geometric gluing.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Descend compatible units and finite multiplicative laws while retaining the model arrows. -/
theorem exists_finite_diagram_unit_model {A : Type u} [CommRing A]
    {I : Type v} [SmallCategory I] [FinCategory I] (B : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : I → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [∀ i, (P i).HasCoeffs A₀]
    (φ : ∀ {i j}, (i ⟶ j) → (B i →ₐ[A] B j))
    (ψ : ∀ {i j}, (i ⟶ j) →
      ((P i).ModelOfHasCoeffs A₀ →ₐ[A₀] (P j).ModelOfHasCoeffs A₀))
    (hψ : ∀ {i j} (f : i ⟶ j) b, (P j).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ ψ f b) =
      φ f ((P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (K L : I → Type v) [∀ i, Finite (K i)] [∀ i, Finite (L i)]
    (x : ∀ i, K i → (B i)ˣ) (τ : ∀ {i j}, (i ⟶ j) → K i → K j)
    (hx : ∀ {i j} (f : i ⟶ j) k, φ f (x i k : B i) = (x j (τ f k) : B j))
    (a b c : ∀ i, L i → K i)
    (hmul : ∀ i l, x i (a i l) * x i (b i l) = x i (c i l))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : ∀ i, (P i).HasCoeffs S,
        ∃ y : ∀ i, K i → ((P i).ModelOfHasCoeffs S)ˣ,
          (∀ i k, (P i).tensorModelOfHasCoeffsEquiv S
            (1 ⊗ₜ (y i k : (P i).ModelOfHasCoeffs S)) = (x i k : B i)) ∧
          (∀ {i j} (f : i ⟶ j) k,
            integerModelTransportHom (P i) (P j) h (ψ f) (y i k) =
              (y j (τ f k) : (P j).ModelOfHasCoeffs S)) ∧
          ∀ i l, y i (a i l) * y i (b i l) = y i (c i l) := by
  classical
  obtain ⟨R, hR, _, h₀R, hPR, y, hy⟩ :=
    exists_integer_model_finite_units B n m P A₀ K x ∅ Set.finite_empty
  let := hR
  let := hPR
  let ψR : ∀ {i j}, (i ⟶ j) →
      ((P i).ModelOfHasCoeffs R →ₐ[R] (P j).ModelOfHasCoeffs R) :=
    fun {i j} f ↦ integerModelTransportHom (P i) (P j) h₀R (ψ f)
  let T := fun j ↦ (Σ i : I, (i ⟶ j) × K i) ⊕ L j
  let v : ∀ j, T j → (P j).ModelOfHasCoeffs R := fun j ↦ Sum.elim
    (fun ⟨_, f, k⟩ ↦ ψR f (y _ k))
    (fun l ↦ (y j (a j l) : (P j).ModelOfHasCoeffs R) * y j (b j l))
  let w : ∀ j, T j → (P j).ModelOfHasCoeffs R := fun j ↦ Sum.elim
    (fun ⟨_, f, k⟩ ↦ y j (τ f k)) (fun l ↦ y j (c j l))
  have hvw (j) (t : T j) : (P j).tensorModelOfHasCoeffsEquiv R (1 ⊗ₜ v j t) =
      (P j).tensorModelOfHasCoeffsEquiv R (1 ⊗ₜ w j t) := by
    rcases t with ⟨i, f, k⟩ | l
    · change (P j).tensorModelOfHasCoeffsEquiv R
        (1 ⊗ₜ integerModelTransportHom (P i) (P j) h₀R (ψ f) (y i k)) = _
      rw [integerModelTransportHom_recovery (P i) (P j) h₀R (ψ f) (φ f) (hψ f)]
      simpa only [w, Sum.elim_inl, hy] using hx f k
    · change (P j).tensorModelOfHasCoeffsEquiv R
        (1 ⊗ₜ ((y j (a j l) : (P j).ModelOfHasCoeffs R) * y j (b j l))) = _
      rw [← one_mul (1 : A), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
      simpa only [w, Sum.elim_inr, one_mul, hy, Units.val_mul] using
        congrArg (fun z : (B j)ˣ ↦ (z : B j)) (hmul j l)
  obtain ⟨S, hS, hsS, hRS, hPS, heq⟩ :=
    exists_integer_model_finite_element_relations B n m P R T v w hvw s hs
  let := hPS
  let z : ∀ i, K i → ((P i).ModelOfHasCoeffs S)ˣ := fun i k ↦
    Units.map (integerModelTransition (P i) hRS).toMonoidHom (y i k)
  refine ⟨S, hS, hsS, h₀R.trans hRS, hPS, z, ?_, ?_, ?_⟩
  · intro i k
    change (P i).tensorModelOfHasCoeffsEquiv S
      (1 ⊗ₜ integerModelTransition (P i) hRS (y i k)) = _
    rw [integerModelTransition_recovery, hy]
  · intro i j f k
    change integerModelTransportHom (P i) (P j) (h₀R.trans hRS) (ψ f)
      (integerModelTransition (P i) hRS (y i k)) = _
    rw [← integerModelTransportHom_trans (P i) (P j) h₀R hRS,
      integerModelTransportHom_transition]
    exact heq j (.inl ⟨i, f, k⟩)
  · intro i l
    apply Units.ext
    change integerModelTransition (P i) hRS (y i (a i l)) *
      integerModelTransition (P i) hRS (y i (b i l)) =
        integerModelTransition (P i) hRS (y i (c i l))
    simpa only [v, w, Sum.elim_inr, map_mul] using heq i (.inr l)

end FLT.Mazur.Approximation
