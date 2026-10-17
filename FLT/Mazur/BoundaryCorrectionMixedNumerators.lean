/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionMixedBaseChange
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Original kernel corrections from localized mixed classes

Clearing one original denominator gives one shared family of exact boundary
kernel corrections. Subtracting it constructs simultaneous compatible
numerators on all independent charts.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
set_option quotPrecheck false
local notation "K" => mixedCorrectionImage φ p q
local notation "δ" => mixedDiscrepancy p q
local notation "b" => boundaryCoordinates φ
variable (U : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization U S]

/-- A localized mixed class vanishes exactly when one denominator admits an exact correction. -/
theorem localized_mixed_eq_zero_iff_kernel (u : ∀ i, A i) :
    (1 ⊗ₜ[R] (K).mkQ (δ u) : S ⊗[R] ((∀ i j, C i j) ⧸ K)) = 0 ↔
      ∃ (a : U) (z : ∀ i, A i), b z = 0 ∧ δ z = a.val • δ u := by
  change TensorProduct.mk R S _ 1 ((K).mkQ (δ u)) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff U]
  simp only [Submonoid.smul_def, ← map_smul]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz, he⟩ := (Submodule.Quotient.mk_eq_zero K).mp ha
    exact ⟨a, z, hz, he⟩
  · rintro ⟨a, z, hz, he⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero K).mpr ⟨z, hz, he⟩⟩

/-- One simultaneous correction constructs all compatible numerators with exact boundary values. -/
theorem localized_mixed_eq_zero_iff_numerator (u : ∀ i, A i) :
    (1 ⊗ₜ[R] (K).mkQ (δ u) : S ⊗[R] ((∀ i j, C i j) ⧸ K)) = 0 ↔
      ∃ (a : U) (v : ∀ i, A i), b v = a.val • b u ∧ δ v = 0 := by
  rw [localized_mixed_eq_zero_iff_kernel φ p q U S]
  constructor
  · rintro ⟨a, z, hz, he⟩
    refine ⟨a, a.val • u - z, ?_, ?_⟩
    · rw [map_sub, map_smul, hz, sub_zero]
    · rw [map_sub, map_smul, he, sub_self]
  · rintro ⟨a, v, hv, he⟩
    refine ⟨a, a.val • u - v, ?_, ?_⟩
    · rw [map_sub, map_smul, hv, sub_self]
    · rw [map_sub, map_smul, he, sub_zero]

end FLT.Mazur.BoundaryCorrectionIdeal
