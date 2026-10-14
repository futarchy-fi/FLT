/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiCompactGenericFlatOpen
public import FLT.Mazur.SchemeFlatTargetNeighborhood

/-!
# Density of whole-source flat neighborhoods over integral targets

Generic flatness produces a dense open in the original target on which the
entire source is flat. We use the original target's integrality; no reduction
or passage to a prime stratum is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFlatTargetOpen
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- Generic flatness contributes a dense whole-source flat open over an affine integral target. -/
theorem dense_of_affine [IsAffine Y] [IsIntegral Y] [CompactSpace X] :
    Dense (locus f : Set Y) := by
  let g := f ≫ Y.isoSpec.hom
  let j := QuasiCompactGenericFlatOpen.targetMap g
  let _ := QuasiCompactGenericFlatOpen.projection_flat g
  let h := IsPullback.of_horiz_isIso
    (show CommSq (𝟙 X) g f Y.isoSpec.inv from ⟨by simp [g]⟩)
  have H := (IsPullback.of_hasPullback j g).flip.paste_horiz h
  simp only [Category.comp_id] at H
  have hl := opensRange_le_of_isPullback f (j ≫ Y.isoSpec.inv) _ _ H
  exact (j ≫ Y.isoSpec.inv).denseRange.mono hl

/-- A quasi-compact projection to any integral scheme has a dense whole-source flat locus. -/
theorem dense [IsIntegral Y] [QuasiCompact f] : Dense (locus f : Set Y) := by
  obtain ⟨y⟩ := IsIntegral.nonempty (X := Y)
  let i := Y.affineCover.idx y
  obtain ⟨z, _⟩ := Y.affineCover.covers y
  let _ : Nonempty (Y.affineCover.X i) := ⟨z⟩
  let _ := isIntegral_of_isOpenImmersion (Y.affineCover.f i)
  let q := pullback.snd f (Y.affineCover.f i)
  have hd := dense_of_affine q
  obtain ⟨t, ht⟩ := hd.nonempty
  let j := (locus q).ι ≫ Y.affineCover.f i
  have H := (IsPullback.of_hasPullback q (locus q).ι).paste_horiz
    (IsPullback.of_hasPullback f (Y.affineCover.f i))
  let _ : Flat (pullback.snd q (locus q).ι) := projection_flat q
  have hl := opensRange_le_of_isPullback f j _ _ H
  apply (locus f).isOpen.dense
  exact ⟨j ⟨t, ht⟩, hl ⟨⟨t, ht⟩, rfl⟩⟩

/-- In particular this is a nonempty open of the unchanged integral target. -/
theorem nonempty [IsIntegral Y] [QuasiCompact f] : (locus f : Set Y).Nonempty :=
  (dense f).nonempty

end FLT.Mazur.SchemeFlatTargetOpen
