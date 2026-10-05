/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteArrowIntegerModel
public import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Integer models of finite diagrams of affine algebras

A diagram with finitely many objects and arrows descends to one finite-type
integer coefficient ring. Its identities and compositions hold at that
stage, and the tensor-product identifications commute with every arrow.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial CategoryTheory
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Simultaneous affine approximation preserves the full finite diagram,
including identities, compositions, compatibility with base change, and
any prescribed finite families of polynomial equations. -/
theorem exists_integer_model_diagram {A : Type u} [CommRing A]
    {I : Type v} [SmallCategory I] [FinCategory I] (B : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : I → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (φ : ∀ {i j}, (i ⟶ j) → (B i →ₐ[A] B j))
    (hid : ∀ i, φ (𝟙 i) = AlgHom.id A (B i))
    (hcomp : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), φ (f ≫ g) = (φ g).comp (φ f))
    (κ : I → Type v) [∀ i, Finite (κ i)]
    (qext : ∀ i, κ i → MvPolynomial (Fin (n i)) A)
    (hqext : ∀ i k, aeval (P i).val (qext i k) = 0)
    (s : Set A) (hs : s.Finite) :
    ∃ A₀ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₀ ∧ s ⊆ A₀ ∧
      ∃ _hP : ∀ i, (P i).HasCoeffs A₀,
        ∃ φ₀ : ∀ {i j}, (i ⟶ j) →
            ((P i).ModelOfHasCoeffs A₀ →ₐ[A₀] (P j).ModelOfHasCoeffs A₀),
          (∀ i, φ₀ (𝟙 i) = AlgHom.id A₀ _) ∧
          (∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), φ₀ (f ≫ g) = (φ₀ g).comp (φ₀ f)) ∧
          (∀ {i j} (f : i ⟶ j) b,
            (P j).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ φ₀ f b) =
              φ f ((P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b))) ∧
          ∀ i k (q₀ : MvPolynomial (Fin (n i)) A₀),
            map (algebraMap A₀ A) q₀ = qext i k →
              (Ideal.Quotient.mk _ q₀ : (P i).ModelOfHasCoeffs A₀) = 0 := by
  classical
  let E := Σ i j : I, (i ⟶ j)
  let src : E → I := fun e ↦ e.1
  let dst : E → I := fun e ↦ e.2.1
  let x : ∀ {i j}, (i ⟶ j) → Fin (n i) → MvPolynomial (Fin (n j)) A :=
    fun {i j} f a ↦ (P j).σ (φ f ((P i).val a))
  have hx {i j} (f : i ⟶ j) (a) : aeval (P j).val (x f a) =
      φ f ((P i).val a) := (P j).aeval_val_σ _
  let K := fun k ↦ κ k ⊕ (Fin (n k) ⊕
    (Σ i j : I, (i ⟶ j) × (j ⟶ k) × Fin (n i)))
  let q : ∀ k, K k → MvPolynomial (Fin (n k)) A := fun k ↦
    Sum.elim (qext k) (Sum.elim (fun a ↦ x (𝟙 k) a - X a)
      (fun ⟨_, _, f, g, a⟩ ↦ aeval (x g) (x f a) - x (f ≫ g) a))
  have hq (k) (b : K k) : aeval (P k).val (q k b) = 0 := by
    rcases b with b | (a | ⟨i, j, f, g, a⟩)
    · exact hqext k b
    · change aeval (P k).val (x (𝟙 k) a - X a) = 0
      simp only [map_sub, hx, aeval_X, hid, AlgHom.id_apply, sub_self]
    · change aeval (P k).val (aeval (x g) (x f a) - x (f ≫ g) a) = 0
      rw [map_sub, comp_aeval_apply]
      simp only [hx, ← comp_aeval_apply, hcomp, AlgHom.comp_apply, sub_self]
  obtain ⟨A₀, hA₀, hs₀, hP, x₀, hx₀, ⟨ψ, hψ⟩, hz⟩ :=
    exists_integer_model_arrows B n m P src dst (fun e ↦ φ e.2.2) K q hq s hs
  let := hP
  let π := fun i ↦ Ideal.Quotient.mkₐ A₀
    (Ideal.span (Set.range ((P i).relationOfHasCoeffs A₀)))
  let y : ∀ {i j}, (i ⟶ j) → Fin (n i) → MvPolynomial (Fin (n j)) A₀ :=
    fun {i j} f ↦ x₀ ⟨i, j, f⟩
  let φ₀ : ∀ {i j}, (i ⟶ j) →
      ((P i).ModelOfHasCoeffs A₀ →ₐ[A₀] (P j).ModelOfHasCoeffs A₀) :=
    fun {i j} f ↦ ψ ⟨i, j, f⟩
  have hy {i j} (f : i ⟶ j) (a) : map (algebraMap A₀ A) (y f a) = x f a :=
    hx₀ ⟨i, j, f⟩ a
  have hφ {i j} (f : i ⟶ j) (p) : φ₀ f (π i p) = π j (aeval (y f) p) :=
    hψ ⟨i, j, f⟩ p
  have hgen {i j} (f : i ⟶ j) (a) : φ₀ f (π i (X a)) = π j (y f a) := by
    rw [hφ, aeval_X]
  refine ⟨A₀, hA₀, hs₀, hP, φ₀, ?_, ?_, ?_, ?_⟩
  · intro i
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro a
    change φ₀ (𝟙 i) (π i (X a)) = π i (X a)
    rw [hgen, ← sub_eq_zero, ← map_sub]
    apply hz i (.inr (.inl a))
    simp only [map_sub, hy, map_X]
    rfl
  · intro i j k f g
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro a
    change φ₀ (f ≫ g) (π i (X a)) = φ₀ g (φ₀ f (π i (X a)))
    rw [hgen, hgen, hφ]
    symm
    rw [← sub_eq_zero, ← map_sub]
    apply hz k (.inr (.inr ⟨i, j, f, g, a⟩))
    simp only [map_sub, map_aeval_polynomial, hy]
    rfl
  · intro i j f b
    induction b using Quotient.inductionOn' with | _ p => ?_
    change (P j).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ φ₀ f (π i p)) =
      φ f ((P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ π i p))
    rw [hφ]
    simp only [π, Ideal.Quotient.mkₐ_eq_mk, (P j).tensorModelOfHasCoeffsEquiv_tmul,
      (P i).tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul]
    rw [← MvPolynomial.aeval_map_algebraMap A, map_aeval_polynomial]
    simp only [hy, comp_aeval_apply, hx]
    rw [← comp_aeval_apply, MvPolynomial.aeval_map_algebraMap]
  · exact fun i k q₀ hq₀ ↦ hz i (.inl k) q₀ hq₀

end FLT.Mazur.Approximation
