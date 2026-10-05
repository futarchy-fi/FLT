/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonRelationIntegerModel
public import FLT.Mazur.IntegerModelTransition

/-!
# Eventual equality across finitely many coefficient models

Finitely many target models can be enlarged together to enforce vanishing
or equality of maps. This keeps both inverse identities at one stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v w

variable {A : Type u} [CommRing A] {I : Type v} [Finite I]
  (B : I → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  (n m : I → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
  (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [∀ i, (P i).HasCoeffs A₀]

/-- Finite vanishing data in finitely many models vanish at one common stage. -/
theorem exists_common_integer_model_eventual_zero
    (K : I → Type w) [∀ i, Finite (K i)]
    (b : ∀ i, K i → (P i).ModelOfHasCoeffs A₀)
    (hb : ∀ i k, (P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b i k) = 0)
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : ∀ i, (P i).HasCoeffs A₁,
        ∀ i k, integerModelTransition (P i) h (b i k) = 0 := by
  classical
  obtain ⟨t, ht⟩ := A₀.fg_iff_finiteType.mpr inferInstance
  have hl (i) (k) : ∃ p : MvPolynomial (Fin (n i)) A₀,
      Ideal.Quotient.mk _ p = b i k := Ideal.Quotient.mk_surjective (b i k)
  choose p hp using hl
  let q := fun i k ↦ map (algebraMap A₀ A) (p i k)
  have hq (i) (k) : aeval (P i).val (q i k) = 0 := by
    change aeval (P i).val (map (algebraMap A₀ A) (p i k)) = 0
    rw [MvPolynomial.aeval_map_algebraMap]
    have hk := hb i k
    rw [← hp i k, (P i).tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul] at hk
    exact hk
  obtain ⟨A₁, hA₁, hs₁, hP₁, hz⟩ :=
    exists_common_integer_relation_models B n m P K q hq (s ∪ t) (hs.union t.finite_toSet)
  let := hP₁
  have h : A₀ ≤ A₁ := by
    rw [← ht, Algebra.adjoin_le_iff]
    exact fun a ha ↦ hs₁ (Or.inr ha)
  refine ⟨A₁, hA₁, fun a ha ↦ hs₁ (Or.inl ha), h, hP₁, fun i k ↦ ?_⟩
  rw [← hp i k, integerModelTransition_mk]
  exact hz i k _ (map_coefficient_inclusion h (p i k))

/-- Finitely many pairs of maps that agree after recovery agree at one stage. -/
theorem exists_common_integer_model_eventual_hom_eq (C : I → Type u)
    [∀ i, CommRing (C i)] [∀ i, Algebra.FiniteType ℤ (C i)]
    (f g : ∀ i, C i →+* (P i).ModelOfHasCoeffs A₀)
    (hfg : ∀ i c, (P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f i c) =
      (P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g i c))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : ∀ i, (P i).HasCoeffs A₁,
        ∀ i, (integerModelTransition (P i) h).comp (f i) =
          (integerModelTransition (P i) h).comp (g i) := by
  let : ∀ i, Algebra.FinitePresentation ℤ (C i) := fun _ ↦
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let Q := fun i ↦ Algebra.Presentation.ofFinitePresentation ℤ (C i)
  let b := fun i a ↦ f i ((Q i).val a) - g i ((Q i).val a)
  have hb (i) (a) : (P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b i a) = 0 := by
    simp only [b, TensorProduct.tmul_sub, map_sub, hfg, sub_self]
  obtain ⟨A₁, hA₁, hs₁, h, hP₁, hz⟩ :=
    exists_common_integer_model_eventual_zero B n m P A₀ _ b hb s hs
  let := hP₁
  refine ⟨A₁, hA₁, hs₁, h, hP₁, fun i ↦ ?_⟩
  let f₁ := ((integerModelTransition (P i) h).comp (f i)).toIntAlgHom
  let g₁ := ((integerModelTransition (P i) h).comp (g i)).toIntAlgHom
  have hgen (a) : f₁ ((Q i).val a) = g₁ ((Q i).val a) := by
    have ha := hz i a
    change integerModelTransition (P i) h (f i ((Q i).val a) - g i ((Q i).val a)) = 0 at ha
    rw [map_sub, sub_eq_zero] at ha
    exact ha
  ext c
  change f₁ c = g₁ c
  rw [← (Q i).aeval_val_σ c, comp_aeval_apply, comp_aeval_apply]
  simp only [hgen]

end FLT.Mazur.Approximation
