/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianProperStructureSheaf
public import FLT.Mazur.ProperSmoothAffineFunctions

/-!
# Actual structure sheaves over arbitrary original bases

Affine locality glues the comparison for proper smooth connected pointed
families over any scheme. It retains the structural pullback on every open
and applies after arbitrary cartesian base change.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.ProperSmoothStructureSheaf

variable {X S : Scheme.{0}} (f : X ⟶ S)
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 _)

include s hs in
/-- Structural pullback is invertible on each affine open of an arbitrary base. -/
lemma affine_app_isIso (U : S.Opens) (hU : IsAffineOpen U) : IsIso (f.app U) := by
  let _ : IsAffine U.toScheme := hU
  let h := (isPullback_morphismRestrict f U).flip
  have H := ProperSmoothAffineFunctions.appTop_bijective (f ∣_ U)
    (ArtinianProperAffineBaseChange.sectionOfSquare h s hs)
    (ArtinianProperAffineBaseChange.sectionOfSquare_projection h s hs)
  have : IsIso (f ∣_ U).appTop := (ConcreteCategory.isIso_iff_bijective _).mpr H
  rw [morphismRestrict_appTop] at this
  change IsIso (f.app (U.ι ''ᵁ ⊤) ≫
    X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) at this
  rw [isIso_comp_right_iff] at this
  convert this using 1 <;> rw [U.ι_image_top]

include s hs in
/-- The actual map of structure sheaves is an isomorphism over every original base. -/
lemma structureMap_isIso :
    IsIso (ArtinianProperStructureSheaf.structureMap (q := f)) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : S.affineOpens ↦ U.val)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using S.isBasis_affineOpens)
  intro U
  exact affine_app_isIso f s hs U.val U.property

/-- The relative structure-sheaf comparison without conditions on the original base. -/
def structureSheafIso : S.sheaf ≅
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := by
  let _ := structureMap_isIso f s hs
  exact asIso (ArtinianProperStructureSheaf.structureMap (q := f))

/-- The sheaf comparison retains the original structural map on each open. -/
lemma structureSheafIso_hom_app (U : S.Opens) :
    (structureSheafIso f s hs).hom.hom.app (op U) = f.app U := rfl

/-- Functions on every inverse-image open come from the corresponding base open. -/
def openSectionsIso (U : S.Opens) : Γ(S, U) ≅ Γ(X, f ⁻¹ᵁ U) :=
  ((sheafToPresheaf _ _).mapIso (structureSheafIso f s hs)).app (op U)

/-- The open-section comparison is the given structural pullback. -/
lemma openSectionsIso_hom (U : S.Opens) : (openSectionsIso f s hs U).hom = f.app U := rfl

include s hs in
/-- Global functions agree over arbitrary original bases, without quasi-compactness. -/
theorem appTop_bijective : Function.Bijective f.appTop :=
  ConcreteCategory.bijective_of_isIso (openSectionsIso f s hs ⊤).hom

include s hs in
/-- The structure-sheaf comparison remains an isomorphism after every cartesian base change. -/
theorem cartesian_structureMap_isIso {P T : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) :
    IsIso (ArtinianProperStructureSheaf.structureMap (q := q)) := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ : Smooth q := MorphismProperty.of_isPullback h inferInstance
  let _ : GeometricallyConnected q := MorphismProperty.of_isPullback h inferInstance
  exact structureMap_isIso q (ArtinianProperAffineBaseChange.sectionOfSquare h s hs)
    (ArtinianProperAffineBaseChange.sectionOfSquare_projection h s hs)

end FLT.Mazur.ProperSmoothStructureSheaf
