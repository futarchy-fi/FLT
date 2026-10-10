/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionLocalLines

/-!
# Normalized neighborhoods as opens of the original base

The image of a normalized neighborhood in an affine atlas chart is an
actual affine open of the base. Transport along the image isomorphism
retains the original chart point and its coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionChartPoints
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas NormalizedSectionLine
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ space M hM) (hs : s ≫ projection M hM = 𝟙 X)

/-- Every base point has a normalized affine neighborhood in an original atlas frame. -/
lemma exists_base_local_line (x : X) :
    ∃ (i : Index M) (U : X.Opens) (hU : IsAffine U.toScheme) (h : U ≤ i.val),
      x ∈ U ∧ let _ := hU
      ∃ (k : coordinates M i) (L : Chart Γ(U.toScheme, ⊤) (coordinates M i) k),
        X.homOfLE h ≫ point M hM s hs i =
          ProjectiveSpace.affineSectionLinePoint (X.homOfLE h).appTop.hom k L := by
  obtain ⟨i, hx, _⟩ := exists_mem_le M hM (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hxV, k, L, hp⟩ := exists_local_line M hM s hs i ⟨x, hx⟩
  let _ := hV
  let U := i.val.ι ''ᵁ V
  have hU : IsAffine U.toScheme := (show IsAffineOpen V from hV).image_of_isOpenImmersion i.val.ι
  let _ := hU
  let f := (i.val.ι.isoImage V).inv
  have hf : f ≫ V.ι = X.homOfLE (i.val.ι_image_le V) :=
    Scheme.Opens.isoImage_ι_inv_ι i.val V
  refine ⟨i, U, hU, i.val.ι_image_le V, ⟨⟨x, hx⟩, hxV, rfl⟩,
    k, baseChange f.appTop.hom k L, ?_⟩
  rw [← hf, Category.assoc, hp, ProjectiveSpace.affineSectionLinePoint_pullback]
  congr 1

end FLT.Mazur.DualAtlasSectionChartPoints
