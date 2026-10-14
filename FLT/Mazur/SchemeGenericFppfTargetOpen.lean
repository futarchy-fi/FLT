/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeGenericFlatTargetOpen
public import FLT.Mazur.SchemeFppfTargetOpen

/-!
# Nonempty fppf regions of dominant projections to integral targets

Density of the full-source flat locus and dominance of the original projection
prove density of its actual fppf region. This is an open in the unchanged
integral target, not a reduced stratum substituted for that target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFppfTargetOpen
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  [QuasiCompact f] [IsIntegral Y] [IsDominant f]

/-- The actual fppf locus is dense, without a global flatness or surjectivity premise. -/
theorem dense : Dense (locus f : Set Y) := by
  rw [coe_locus]
  exact f.denseRange.inter_of_isOpen_right (SchemeFlatTargetOpen.dense f)
    (SchemeFlatTargetOpen.locus f).isOpen

/-- The constructed fppf target contains points of the original integral model. -/
theorem nonempty : (locus f : Set Y).Nonempty := (dense f).nonempty

/-- Every nonempty target open contains an actual fppf-region point. -/
theorem inter_nonempty (U : Y.Opens) (hU : (U : Set Y).Nonempty) :
    ((U ⊓ locus f : Y.Opens) : Set Y).Nonempty :=
  (dense f).inter_open_nonempty U U.isOpen hU

/-- Such a point has an original source preimage, retaining the original morphism. -/
theorem exists_source (U : Y.Opens) (hU : (U : Set Y).Nonempty) :
    ∃ x : X, f x ∈ U ∧ f x ∈ locus f := by
  obtain ⟨y, hyU, hy⟩ := inter_nonempty f U hU
  have hi : y ∈ Set.range f := by
    rw [coe_locus] at hy
    exact hy.1
  obtain ⟨x, rfl⟩ := hi
  exact ⟨x, hyU, hy⟩

/-- The actual constructed full source is nonempty, not merely its abstract image. -/
theorem source_nonempty : Nonempty (source f) := by
  obtain ⟨y, hy⟩ := nonempty f
  obtain ⟨x, _⟩ := (projection f).surjective ⟨y, hy⟩
  exact ⟨x⟩

/-- After any open target restriction the actual fppf region remains dense, even if empty. -/
theorem dense_open_baseChange {Z : Scheme.{0}} (j : Z ⟶ Y) [IsOpenImmersion j] :
    Dense (locus (pullback.snd f j) : Set Z) := by
  by_cases hZ : Nonempty Z
  · let _ := hZ
    let _ := isIntegral_of_isOpenImmersion j
    let _ : IsDominant (pullback.snd f j) :=
      IsZariskiLocalAtTarget.of_isPullback (IsPullback.of_hasPullback f j) inferInstance
    exact dense (pullback.snd f j)
  · intro z
    exact (hZ ⟨z⟩).elim

/-- Restricting to the fppf region loses no nonempty open target restriction. -/
theorem nonempty_open_baseChange_iff {Z : Scheme.{0}} (j : Z ⟶ Y)
    [IsOpenImmersion j] :
    (locus (pullback.snd f j) : Set Z).Nonempty ↔ Nonempty Z := by
  refine ⟨fun ⟨z, _⟩ ↦ ⟨z⟩, fun hZ ↦ ?_⟩
  let _ := hZ
  exact (dense_open_baseChange f j).nonempty

end FLT.Mazur.SchemeFppfTargetOpen
