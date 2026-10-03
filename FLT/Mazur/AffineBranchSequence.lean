/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleExact
public import FLT.Mazur.StructureDirectImageSections

/-!
# The normalization sequence on affine spectra

Compute the actual structure-module inclusion and branch restrictions on global
sections, then transport ring exactness to short exactness of the module sheaves.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.AffineBranchSequence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open StructureDirectImage PolygonStructureInclusion
variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (a b : S ⟶ T) (q : R ⟶ T)
  (ha : Spec.map a ≫ Spec.map f = Spec.map q)
  (hb : Spec.map b ≫ Spec.map f = Spec.map q)
/-- Restriction of normalization functions along one affine branch. -/
abbrev branch (a : S ⟶ T) (ha : Spec.map a ≫ Spec.map f = Spec.map q) :
    image (Spec.map f) ⟶ image (Spec.map q) :=
  restriction (Spec.map a) (Spec.map f) (Spec.map q)
    ha
/-- The oriented difference between the two branch restrictions. -/
def difference : image (Spec.map f) ⟶ image (Spec.map q) :=
  branch f q a ha - branch f q b hb
@[reassoc] theorem unit_branch (a : S ⟶ T) (ha : Spec.map a ≫ Spec.map f = Spec.map q) :
    unitMap (Spec.map f) ≫ branch f q a ha = unitMap (Spec.map q) :=
  unitMap_restriction _ _ _ _
@[reassoc] theorem unit_difference :
    unitMap (Spec.map f) ≫ difference f a b q ha hb = 0 := by
  rw [difference, Preadditive.comp_sub, unit_branch, unit_branch, sub_self]
/-- The actual affine normalization sequence of module sheaves. -/
def complex : ShortComplex (Spec R).Modules :=
  ShortComplex.mk (unitMap (Spec.map f)) (difference f a b q ha hb)
    (unit_difference f a b q ha hb)
theorem branch_sections (a : S ⟶ T) (ha : Spec.map a ≫ Spec.map f = Spec.map q)
    (r : (image (Spec.map f)).val.obj (.op ⊤)) :
    spectrumSections q ((branch f q a ha).val.app (.op ⊤) r) =
      a (spectrumSections f r) :=
  spectrumSections_restriction f a q ha r
private theorem sub_apply {X : Scheme.{u}} {M N : X.Modules} (α β : M ⟶ N)
    (U : X.Opens) (r : M.val.obj (.op U)) :
    (α - β).val.app (.op U) r = α.val.app (.op U) r - β.val.app (.op U) r := rfl
theorem difference_sections (r : (image (Spec.map f)).val.obj (.op ⊤)) :
    spectrumSections q ((difference f a b q ha hb).val.app (.op ⊤) r) =
      a (spectrumSections f r) - b (spectrumSections f r) := by
  rw [difference, sub_apply, map_sub, branch_sections, branch_sections]
/-- A ring equalizer with surjective branch difference gives a sheaf short exact sequence. -/
theorem shortExact (hi : Function.Injective f)
    (he : ∀ s : S, a s = b s → ∃ r : R, f r = s)
    (hs : Function.Surjective (fun s : S ↦ a s - b s)) :
    (complex f a b q ha hb).ShortExact := by
  let : IsIso (complex f a b q ha hb).X₁.fromTildeΓ :=
    inferInstanceAs (IsIso (structureModule (Spec R)).fromTildeΓ)
  let : IsIso (complex f a b q ha hb).X₂.fromTildeΓ :=
    isIso_fromTildeΓ_pushforward f (structureModule (Spec S))
  let : IsIso (complex f a b q ha hb).X₃.fromTildeΓ :=
    isIso_fromTildeΓ_pushforward q (structureModule (Spec T))
  apply AffineModuleExact.shortExact_of_sections
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro s hz
    have hz' : a (spectrumSections f s) = b (spectrumSections f s) := by
      apply sub_eq_zero.mp
      rw [← difference_sections f a b q ha hb]
      have hz0 : (difference f a b q ha hb).val.app (.op ⊤) s = 0 := hz
      exact (congrArg (spectrumSections q) hz0).trans (map_zero _)
    obtain ⟨r, hr⟩ := he _ hz'
    refine ⟨(Scheme.ΓSpecIso R).inv r, ?_⟩
    apply (spectrumSections f).injective
    change spectrumSections f ((unitMap (Spec.map f)).val.app (.op ⊤) _) = _
    rw [spectrumSections_unitMap]
    exact ((congrArg f ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.apply_symm_apply r))).trans hr
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    apply hi
    have hh := congrArg (spectrumSections f) hxy
    change spectrumSections f ((unitMap (Spec.map f)).val.app (.op ⊤) x) =
      spectrumSections f ((unitMap (Spec.map f)).val.app (.op ⊤) y) at hh
    exact (spectrumSections_unitMap f x).symm.trans
      (hh.trans (spectrumSections_unitMap f y))
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro t
    obtain ⟨s, hs⟩ := hs (spectrumSections q t)
    refine ⟨(spectrumSections f).symm s, ?_⟩
    apply (spectrumSections q).injective
    change spectrumSections q ((difference f a b q ha hb).val.app (.op ⊤) _) = _
    rw [difference_sections, AddEquiv.apply_symm_apply]
    exact hs
end FLT.Mazur.AffineBranchSequence
