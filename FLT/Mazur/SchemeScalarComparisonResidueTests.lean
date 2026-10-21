/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarComparisonLocalGeometry
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Full comparison coverage by residue-field relation tests

A kernel-pair point carries two maps from its own residue field, not merely
two underlying source points. On a local etale image neighborhood, coverage
is equivalent to an actual relation arrow with both of these coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarComparisonResidueTests
open SchemeScalarImageQuotient SchemeComparisonCoverageLocus
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {D X : Scheme.{0}}
  (f : X ⟶ Spec (.of R)) (a b : D ⟶ X) (h : a ≫ f = b ≫ f)
  (U : (Spec (.of (Scalars f))).Opens)
set_option quotPrecheck false
local notation "c" => projection f
local notation "u" => pullback.fst f f
local notation "v" => pullback.snd f f
local notation "k" => pullback.lift a b h
local notation "m" => u ≫ c
local notation "W" => m ⁻¹ᵁ U
local notation "kU" => k ∣_ W

/-- The two residue-field endpoints satisfy the unchanged original scalar equations. -/
theorem residue_endpoint_condition (w : (W).toScheme) :
    (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ u ≫ f =
      (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ v ≫ f := by
  rw [pullback.condition]

variable [Etale a] [Etale ((projection f) ∣_ U)] [Mono (pullback.lift a b h)]

/-- A covered full kernel point is precisely an actual arrow on both residue-field coordinates. -/
theorem mem_range_iff_residue_arrow (w : (W).toScheme) :
    w.val ∈ Set.range k ↔
      ∃ d : Spec ((W).toScheme.residueField w) ⟶ D,
        d ≫ a = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ u ∧
        d ≫ b = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ v := by
  let _ := SchemeScalarComparisonLocalGeometry.comparison_isOpenImmersion f a b h U
  let t := (W).toScheme.fromSpecResidueField w
  constructor
  · intro hw
    have ht : Set.range t ⊆ Set.range kU := by
      rw [Scheme.range_fromSpecResidueField]
      exact Set.singleton_subset_iff.mpr ((mem_restricted_range_iff k m U w).mpr hw)
    let l := IsOpenImmersion.lift kU t ht
    have hl : l ≫ kU = t := IsOpenImmersion.lift_fac _ _ _
    have hd : (l ≫ (k ⁻¹ᵁ W).ι) ≫ k = t ≫ (W).ι := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hl]
    refine ⟨l ≫ (k ⁻¹ᵁ W).ι, ?_, ?_⟩
    · simpa only [Category.assoc, pullback.lift_fst] using congrArg (fun g ↦ g ≫ u) hd
    · simpa only [Category.assoc, pullback.lift_snd] using congrArg (fun g ↦ g ≫ v) hd
  · rintro ⟨d, ha, hb⟩
    have hd : d ≫ k = t ≫ (W).ι := by
      apply (IsPullback.of_hasPullback f f).hom_ext
      · simpa only [Category.assoc, pullback.lift_fst] using ha
      · simpa only [Category.assoc, pullback.lift_snd] using hb
    refine ⟨d default, ?_⟩
    have hp := congrArg (fun g : Spec ((W).toScheme.residueField w) ⟶ pullback f f ↦
      g default) hd
    simpa only [Scheme.Hom.comp_apply, t, Scheme.fromSpecResidueField_apply,
      Scheme.Opens.ι_apply] using hp

/-- Testing both residue-field endpoints gives exactly full original fiber coverage. -/
theorem fiber_coverage_iff_residue_arrows (z : Spec (.of (Scalars f))) (hz : z ∈ U) :
    (∀ w : (pullback f f : Scheme), m w = z → w ∈ Set.range k) ↔
      ∀ w : (W).toScheme, m w.val = z →
        ∃ d : Spec ((W).toScheme.residueField w) ⟶ D,
          d ≫ a = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ u ∧
          d ≫ b = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ v := by
  constructor
  · intro hc w hw
    exact (mem_range_iff_residue_arrow f a b h U w).mp (hc w.val hw)
  · intro ht w hw
    have hwU : w ∈ W := by change m w ∈ U; rw [hw]; exact hz
    exact (mem_range_iff_residue_arrow f a b h U ⟨w, hwU⟩).mpr (ht ⟨w, hwU⟩ hw)

/-- Actual residue-field arrows construct a smaller full comparison neighborhood. -/
theorem exists_neighborhood_of_residue_arrows [IsIntegralHom ((projection f) ∣_ U)]
    (z : Spec (.of (Scalars f))) (hz : z ∈ U)
    (ht : ∀ w : (W).toScheme, m w.val = z →
      ∃ d : Spec ((W).toScheme.residueField w) ⟶ D,
        d ≫ a = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ u ∧
        d ≫ b = (W).toScheme.fromSpecResidueField w ≫ (W).ι ≫ v) :
    ∃ V : (Spec (.of (Scalars f))).Opens, V ≤ U ∧ z ∈ V ∧
      Etale (c ∣_ V) ∧ IsIntegralHom (c ∣_ V) ∧ Surjective (k ∣_ (m ⁻¹ᵁ V)) :=
  SchemeScalarComparisonLocalGeometry.exists_neighborhood f a b h U z hz
    ((fiber_coverage_iff_residue_arrows f a b h U z hz).mpr ht)

end FLT.Mazur.SchemeScalarComparisonResidueTests
