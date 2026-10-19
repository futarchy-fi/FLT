/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedOpenInclusion

/-!
# Unit loci under locally ringed open restriction

The section transport for an actual open restriction preserves unit loci.
Thus the basic open of the transported global section is precisely the
inverse image of the ambient basic open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.LocallyRingedOpenInclusion
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : LocallyRingedSpace.{u}) (W : Opens X) (s : X.presheaf.obj (op W))

/-- Open-section transport preserves the actual locally ringed unit locus. -/
theorem sectionsIso_basicOpen :
    (X.restrict W.isOpenEmbedding).toRingedSpace.basicOpen ((sectionsIso X W).inv s) =
      (Opens.map (X.ofRestrict W.isOpenEmbedding).base).obj (X.toRingedSpace.basicOpen s) := by
  have ht : (Opens.map (X.ofRestrict W.isOpenEmbedding).base).obj W = ⊤ :=
    Opens.inclusion'_map_eq_top W
  have hs : (sectionsIso X W).inv =
      (X.ofRestrict W.isOpenEmbedding).c.app (op W) ≫
        (X.restrict W.isOpenEmbedding).presheaf.map (eqToHom (congrArg op ht)) := by
    change X.presheaf.map _ = X.presheaf.map _ ≫ X.presheaf.map _
    rw [← Functor.map_comp]
    congr 1
  rw [hs, CommRingCat.comp_apply]
  erw [RingedSpace.basicOpen_res_eq]
  exact (LocallyRingedSpace.preimage_basicOpen (X.ofRestrict W.isOpenEmbedding) s).symm

/-- The basic open in the restriction has exactly the original ambient image. -/
theorem sectionsIso_basicOpen_image :
    (X.ofRestrict W.isOpenEmbedding).base ''
      ((X.restrict W.isOpenEmbedding).toRingedSpace.basicOpen
        ((sectionsIso X W).inv s) : Set _) = (X.toRingedSpace.basicOpen s).carrier := by
  rw [sectionsIso_basicOpen]
  change Subtype.val '' (Subtype.val ⁻¹' (X.toRingedSpace.basicOpen s).carrier) = _
  apply Set.image_preimage_eq_of_subset
  rintro x hx
  exact ⟨⟨x, RingedSpace.basicOpen_le _ s hx⟩, rfl⟩

end FLT.Mazur.LocallyRingedOpenInclusion
