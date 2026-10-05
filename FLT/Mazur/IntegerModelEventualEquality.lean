/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelTransition

/-!
# Eventual equality in coefficient models

Finitely many elements that vanish in the original algebra vanish after
one common enlargement of the coefficient stage. Consequently maps from a
finite-type integer algebra which agree after recovery agree at a later
stage. Quotient transition maps need not be injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
  (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]

/-- Finite vanishing data in a fixed model vanish after a common enlargement. -/
theorem exists_integer_model_eventual_zero {κ : Type v} [Finite κ]
    (b : κ → P.ModelOfHasCoeffs A₀)
    (hb : ∀ k, P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b k) = 0)
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁,
        ∀ k, integerModelTransition P h (b k) = 0 := by
  classical
  obtain ⟨t, ht⟩ := A₀.fg_iff_finiteType.mpr inferInstance
  have hl (k) : ∃ p : MvPolynomial (Fin n) A₀, Ideal.Quotient.mk _ p = b k :=
    Ideal.Quotient.mk_surjective (b k)
  choose p hp using hl
  let q := fun k ↦ map (algebraMap A₀ A) (p k)
  have hq (k) : aeval P.val (q k) = 0 := by
    change aeval P.val (map (algebraMap A₀ A) (p k)) = 0
    rw [MvPolynomial.aeval_map_algebraMap]
    have hk := hb k
    rw [← hp k, P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul] at hk
    exact hk
  obtain ⟨A₁, hA₁, hs₁, hP₁, q₁, hq₁, hz⟩ :=
    exists_integer_model_relations P q hq (s ∪ t) (hs.union t.finite_toSet)
  let := hP₁
  have h : A₀ ≤ A₁ := by
    rw [← ht, Algebra.adjoin_le_iff]
    exact fun a ha ↦ hs₁ (Or.inr ha)
  refine ⟨A₁, hA₁, fun a ha ↦ hs₁ (Or.inl ha), h, hP₁, fun k ↦ ?_⟩
  rw [← hp k, integerModelTransition_mk]
  have heq : map (Subalgebra.inclusion h).toRingHom (p k) = q₁ k := by
    apply MvPolynomial.map_injective (f := algebraMap A₁ A) Subtype.val_injective
    rw [map_coefficient_inclusion, hq₁]
  rw [heq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hz k)

/-- Maps from a fixed finite-type integer algebra that agree after recovery
become equal after enlarging the coefficient model of their common target. -/
theorem exists_integer_model_eventual_hom_eq {C : Type u} [CommRing C]
    [Algebra.FiniteType ℤ C] (f g : C →+* P.ModelOfHasCoeffs A₀)
    (hfg : ∀ c, P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f c) =
      P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g c)) (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁,
        (integerModelTransition P h).comp f = (integerModelTransition P h).comp g := by
  let : Algebra.FinitePresentation ℤ C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let Q := Algebra.Presentation.ofFinitePresentation ℤ C
  let b := fun i ↦ f (Q.val i) - g (Q.val i)
  have hb (i) : P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b i) = 0 := by
    simp only [b, TensorProduct.tmul_sub, map_sub, hfg, sub_self]
  obtain ⟨A₁, hA₁, hs₁, h, hP₁, hz⟩ :=
    exists_integer_model_eventual_zero P A₀ b hb s hs
  let := hP₁
  let f₁ := ((integerModelTransition P h).comp f).toIntAlgHom
  let g₁ := ((integerModelTransition P h).comp g).toIntAlgHom
  have hgen (i) : f₁ (Q.val i) = g₁ (Q.val i) := by
    have hi := hz i
    change integerModelTransition P h (f (Q.val i) - g (Q.val i)) = 0 at hi
    rw [map_sub, sub_eq_zero] at hi
    exact hi
  refine ⟨A₁, hA₁, hs₁, h, hP₁, ?_⟩
  ext c
  change f₁ c = g₁ c
  rw [← Q.aeval_val_σ c, comp_aeval_apply, comp_aeval_apply]
  simp only [hgen]

end FLT.Mazur.Approximation
