/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.AugmentationCotangent
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Choosing minimal coordinates from a generating family -/

@[expose] public noncomputable section

universe v

namespace AlgHom

open MvPolynomial

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- Algebra generators span the augmentation cotangent space. -/
theorem span_augmentationCotangent_eq_top (ε : A →ₐ[k] k) {ι : Type*}
    (x : ι → A) (hx : Function.Surjective (aeval (R := k) x)) :
    Submodule.span k (Set.range (fun i ↦ ε.augmentationCotangent (x i))) = ⊤ := by
  let S := Submodule.span k (Set.range (fun i ↦ ε.augmentationCotangent (x i)))
  have hmem (f : MvPolynomial ι k) : ε.augmentationCotangent (aeval x f) ∈ S := by
    induction f using MvPolynomial.induction_on with
    | C c =>
      simp only [aeval_C, Algebra.algebraMap_eq_smul_one, map_smul,
        augmentationCotangent_one, smul_zero]
      exact S.zero_mem
    | add f g hf hg => simpa only [map_add] using S.add_mem hf hg
    | mul_X f i hf =>
      rw [map_mul, aeval_X, augmentationCotangent_mul]
      exact S.add_mem
        (S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)) (S.smul_mem _ hf)
  apply top_unique
  intro t _
  obtain ⟨a, rfl⟩ := (RingHom.ker ε).toCotangent_surjective t
  obtain ⟨f, hf⟩ := hx a
  have h := hmem f
  rw [hf, ε.augmentationCotangent_of_mem] at h
  exact h

variable [Module.Finite k A] [IsLocalRing A]

/-- Any prescribed lifts of a cotangent basis generate the finite local algebra. -/
theorem aeval_surjective_of_cotangent_basis (ε : A →ₐ[k] k) {ι : Type*}
    (x : ι → RingHom.ker ε) (b : Module.Basis ι k (RingHom.ker ε).Cotangent)
    (hb : ∀ i, (RingHom.ker ε).toCotangent (x i) = b i) :
    Function.Surjective (aeval (R := k) (fun i ↦ (x i : A))) := by
  let : IsNoetherianRing A := IsNoetherianRing.of_finite k A
  have hspan : Ideal.span (Set.range (fun i ↦ (x i : A))) = RingHom.ker ε := by
    apply Ideal.span_eq_of_span_toCotangent_eq_top _ (IsNoetherian.noetherian _)
    · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε)
    · apply Submodule.span_eq_top_of_span_eq_top k A
      simpa only [hb] using b.span_eq
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact ε.adjoin_eq_top_of_span_augmentation x hspan

/-- A generating family contains a subfamily lifting a cotangent basis,
which itself still generates the entire finite local algebra. -/
theorem exists_cotangent_basis_subfamily (ε : A →ₐ[k] k) {ι : Type v}
    (x : ι → A) (hx : ∀ i, ε (x i) = 0)
    (hsurj : Function.Surjective (aeval (R := k) x)) :
    ∃ (κ : Type v) (a : κ → ι), Function.Injective a ∧
      ∃ b : Module.Basis κ k (RingHom.ker ε).Cotangent,
        (∀ j, ε.augmentationCotangent (x (a j)) = b j) ∧
        Function.Surjective (aeval (R := k) (x ∘ a)) := by
  obtain ⟨κ, a, ha, hspan, hlin⟩ := exists_linearIndependent' k
    (fun i ↦ ε.augmentationCotangent (x i))
  rw [ε.span_augmentationCotangent_eq_top x hsurj] at hspan
  let b : Module.Basis κ k (RingHom.ker ε).Cotangent :=
    Module.Basis.mk hlin hspan.ge
  have hb (j : κ) : ε.augmentationCotangent (x (a j)) = b j :=
    (Module.Basis.mk_apply hlin hspan.ge j).symm
  refine ⟨κ, a, ha, b, hb, ?_⟩
  apply ε.aeval_surjective_of_cotangent_basis
    (fun j ↦ ⟨x (a j), hx (a j)⟩) b
  intro j
  exact (ε.augmentationCotangent_of_mem ⟨x (a j), hx (a j)⟩).symm.trans (hb j)

end AlgHom
