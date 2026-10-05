/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteDiagramIntegerModel
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite affine diagrams with principal open covers

A unit-ideal witness for each finite principal cover is polynomial data.
Descending those witnesses along with the diagram preserves the covers at
the same stage, rather than only after base change.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial CategoryTheory
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

/-- Descend a finite affine diagram and chosen finite principal covers
simultaneously, retaining both diagram laws and the cover conditions. -/
theorem exists_integer_model_diagram_covers {A : Type u} [CommRing A]
    {I : Type v} [SmallCategory I] [FinCategory I] (B : I → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (n m : I → ℕ) (P : ∀ i, Algebra.Presentation A (B i) (Fin (n i)) (Fin (m i)))
    (φ : ∀ {i j}, (i ⟶ j) → (B i →ₐ[A] B j))
    (hid : ∀ i, φ (𝟙 i) = AlgHom.id A (B i))
    (hcomp : ∀ {i j k} (f : i ⟶ j) (g : j ⟶ k), φ (f ≫ g) = (φ g).comp (φ f))
    (K : I → Type v) [∀ i, Finite (K i)] (x : ∀ i, K i → B i)
    (hcover : ∀ i, (⨆ a, PrimeSpectrum.basicOpen (x i a)) = ⊤)
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
          ∃ x₀ : ∀ i, K i → (P i).ModelOfHasCoeffs A₀,
            (∀ i a, (P i).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x₀ i a) = x i a) ∧
            ∀ i, (⨆ a, PrimeSpectrum.basicOpen (x₀ i a)) = ⊤ := by
  classical
  let := fun i ↦ Fintype.ofFinite (K i)
  have hw (i) : ∃ c : K i → B i, ∑ a, c a * x i a = 1 := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp (hcover i)]
    trivial
  choose c hc using hw
  let z := fun i ↦ Sum.elim (fun a ↦ (P i).σ (x i a)) (fun a ↦ (P i).σ (c i a))
  let q := fun i (_ : PUnit.{v + 1}) ↦
    (∑ a, z i (.inr a) * z i (.inl a)) - 1
  have hq (i) (k) : aeval (P i).val (q i k) = 0 := by
    simp only [q, z, map_sub, map_sum, map_mul, map_one,
      (P i).aeval_val_σ, hc, sub_self, Sum.elim_inl, Sum.elim_inr]
  let t : Set A := s ∪ ⋃ i, ⋃ a, (z i a).coeffs
  have ht : t.Finite := hs.union (Set.finite_iUnion fun i ↦
    Set.finite_iUnion fun a ↦ (z i a).coeffs.finite_toSet)
  obtain ⟨A₀, hA₀, ht₀, hP, φ₀, hid₀, hcomp₀, hbase, hz⟩ :=
    exists_integer_model_diagram B n m P φ hid hcomp (fun _ ↦ PUnit.{v + 1}) q hq t ht
  let := hP
  have hl (i) (a : K i ⊕ K i) : z i a ∈ Set.range (map (algebraMap A₀ A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro b hb
    exact ⟨⟨b, ht₀ (Or.inr (Set.mem_iUnion.mpr ⟨i,
      Set.mem_iUnion.mpr ⟨a, hb⟩⟩))⟩, rfl⟩
  choose z₀ hz₀ using hl
  let π := fun i ↦ Ideal.Quotient.mkₐ A₀
    (Ideal.span (Set.range ((P i).relationOfHasCoeffs A₀)))
  refine ⟨A₀, hA₀, fun a ha ↦ ht₀ (Or.inl ha), hP, φ₀, hid₀, hcomp₀, hbase,
    fun i a ↦ π i (z₀ i (.inl a)), ?_, ?_⟩
  · intro i a
    change (P i).tensorModelOfHasCoeffsEquiv A₀
      (1 ⊗ₜ Ideal.Quotient.mk _ (z₀ i (.inl a))) = x i a
    rw [(P i).tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
      ← MvPolynomial.aeval_map_algebraMap A, hz₀]
    exact (P i).aeval_val_σ _
  · intro i
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Ideal.eq_top_iff_one]
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    refine ⟨fun a ↦ π i (z₀ i (.inr a)), ?_⟩
    have hzero := hz i PUnit.unit ((∑ a, z₀ i (.inr a) * z₀ i (.inl a)) - 1)
      (by simp only [map_sub, map_sum, map_mul, map_one, hz₀]; rfl)
    change π i ((∑ a, z₀ i (.inr a) * z₀ i (.inl a)) - 1) = 0 at hzero
    simpa only [map_sub, map_sum, map_mul, map_one, sub_eq_zero] using hzero

end FLT.Mazur.Approximation
