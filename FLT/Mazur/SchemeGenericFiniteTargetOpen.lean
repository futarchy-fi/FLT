/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiCompactGenericFiniteOpen
public import FLT.Mazur.SchemeFiniteTargetRestriction

/-!
# Dense whole-source finite neighborhoods over integral targets

Every separated quasi-finite morphism of finite presentation has a dense
finite target locus over an integral target. The construction keeps the
original target and every source component above the resulting open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An open Cartesian finite presentation contributes its whole target image. -/
theorem opensRange_le_finiteTarget_of_isPullback {X Y Z P : Scheme}
    (f : X ⟶ Y) (j : Z ⟶ Y) [IsOpenImmersion j]
    (a : P ⟶ X) (p : P ⟶ Z) (h : IsPullback a p f j) [IsFinite p] :
    j.opensRange ≤ finiteTargetOpen f := by
  let e := j.isoOpensRange
  have he : e.inv ≫ j = j.opensRange.ι := Scheme.Hom.isoOpensRange_inv_comp j
  have h₁ := IsPullback.of_horiz_isIso
    (show CommSq (𝟙 P) (p ≫ e.hom) p e.inv from ⟨by simp⟩)
  have h₂ := h₁.paste_horiz h
  simp only [Category.id_comp, he] at h₂
  let _ : IsFinite (pullback.snd f j.opensRange.ι) := by
    rw [← h₂.isoPullback_inv_snd]
    infer_instance
  apply (le_finiteTargetOpen_iff f _).mpr
  rw [← (isPullback_morphismRestrict f j.opensRange).flip.isoPullback_hom_snd]
  infer_instance

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  [LocallyQuasiFinite f] [IsSeparated f]

/-- Generic finiteness constructs a dense finite locus on an original affine integral target. -/
theorem finiteTargetOpen_dense_of_affine [IsAffine Y] [IsIntegral Y] [CompactSpace X] :
    Dense (finiteTargetOpen f : Set Y) := by
  let g := f ≫ Y.isoSpec.hom
  let j := QuasiCompactGenericFlatOpen.targetMap g
  let _ := QuasiCompactGenericFlatOpen.projection_isFinite g
  let h := IsPullback.of_horiz_isIso
    (show CommSq (𝟙 X) g f Y.isoSpec.inv from ⟨by simp [g]⟩)
  have H := (IsPullback.of_hasPullback j g).flip.paste_horiz h
  simp only [Category.comp_id] at H
  have hl := opensRange_le_finiteTarget_of_isPullback f (j ≫ Y.isoSpec.inv) _ _ H
  exact (j ≫ Y.isoSpec.inv).denseRange.mono hl

/-- The full original projection has a dense finite target locus on any integral base. -/
theorem finiteTargetOpen_dense [IsIntegral Y] [QuasiCompact f] :
    Dense (finiteTargetOpen f : Set Y) := by
  obtain ⟨y⟩ := IsIntegral.nonempty (X := Y)
  let i := Y.affineCover.idx y
  obtain ⟨z, _⟩ := Y.affineCover.covers y
  let _ : Nonempty (Y.affineCover.X i) := ⟨z⟩
  let _ := isIntegral_of_isOpenImmersion (Y.affineCover.f i)
  let q := pullback.snd f (Y.affineCover.f i)
  obtain ⟨t, ht⟩ := (finiteTargetOpen_dense_of_affine q).nonempty
  have hf : IsFinite (q ∣_ finiteTargetOpen q) := finite_restrict_finiteTarget q
  let _ := hf
  let j := (finiteTargetOpen q).ι ≫ Y.affineCover.f i
  have H := (isPullback_morphismRestrict q (finiteTargetOpen q)).flip.paste_horiz
    (IsPullback.of_hasPullback f (Y.affineCover.f i))
  have hl := opensRange_le_finiteTarget_of_isPullback f j _ _ H
  apply (finiteTargetOpen f).isOpen.dense
  exact ⟨j ⟨t, ht⟩, hl ⟨⟨t, ht⟩, rfl⟩⟩

/-- The original generic point has an actual whole-source finite neighborhood. -/
theorem genericPoint_mem_finiteTarget [IsIntegral Y] [QuasiCompact f] :
    genericPoint Y ∈ finiteTargetOpen f := by
  obtain ⟨y, hy⟩ := (finiteTargetOpen_dense f).nonempty
  exact (genericPoint_specializes y).mem_open (finiteTargetOpen f).isOpen hy

end FLT.Mazur.SchemeOpenEnvelope
