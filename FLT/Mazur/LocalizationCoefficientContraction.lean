/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Ideal

/-!
# Contracting ideals through localized coefficient squares

If every denominator descends to the coefficient model, contraction of a
localized ideal is the localization of its contraction. The coefficient map
need not be injective and the original ideal need not be finitely generated.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizationCoefficientContraction

universe u v w z

variable {P₀ : Type u} [CommRing P₀] {P : Type v} [CommRing P]
  {L₀ : Type w} [CommRing L₀] {L : Type z} [CommRing L]
  [Algebra P₀ L₀] [Algebra P L]
  (M₀ : Submonoid P₀) (M : Submonoid P)
  [IsLocalization M₀ L₀] [IsLocalization M L]
  (c : P₀ →+* P) (d : L₀ →+* L)
  (hcomm : d.comp (algebraMap P₀ L₀) = (algebraMap P L).comp c)
  (hM : M₀.map c = M)

include hcomm hM in
/-- Denominator descent identifies the contracted ideal on the coefficient localization. -/
theorem comap_localized_ideal (I : Ideal P) :
    (I.map (algebraMap P L)).comap d = (I.comap c).map (algebraMap P₀ L₀) := by
  apply (IsLocalization.orderEmbedding M₀ L₀).injective
  ext x
  change d (algebraMap P₀ L₀ x) ∈ I.map (algebraMap P L) ↔
    algebraMap P₀ L₀ x ∈ (I.comap c).map (algebraMap P₀ L₀)
  have hx := RingHom.congr_fun hcomm x
  change d (algebraMap P₀ L₀ x) = algebraMap P L (c x) at hx
  rw [hx, IsLocalization.algebraMap_mem_map_algebraMap_iff M,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M₀]
  constructor
  · rintro ⟨m, hm, hmx⟩
    rw [← hM] at hm
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    exact ⟨m₀, hm₀, by simpa only [Ideal.mem_comap, map_mul] using hmx⟩
  · rintro ⟨m₀, hm₀, hmx⟩
    refine ⟨c m₀, hM ▸ ⟨m₀, hm₀, rfl⟩, ?_⟩
    simpa only [Ideal.mem_comap, map_mul] using hmx

end FLT.Mazur.LocalizationCoefficientContraction
