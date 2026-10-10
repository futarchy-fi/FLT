/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianProperRelativeFunctions
public import FLT.Mazur.ArtinianProperStructureSheaf

/-!
# Actual structure-sheaf comparison over locally Noetherian bases

Affine locality extends the nonreduced Noetherian global-functions theorem
to every open of an arbitrary locally Noetherian base. The comparison keeps
the original structure morphism and its section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.NoetherianProperStructureSheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsLocallyNoetherian S]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include s hs in
/-- Structural pullback is invertible on each affine open of a locally Noetherian base. -/
lemma affine_app_isIso (U : S.Opens) (hU : IsAffineOpen U) : IsIso (f.app U) := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let h := (isPullback_morphismRestrict f U).flip
  have H := NoetherianProperRelativeFunctions.appTop_bijective (f ∣_ U)
    (ArtinianProperAffineBaseChange.sectionOfSquare h s hs)
    (ArtinianProperAffineBaseChange.sectionOfSquare_projection h s hs)
  have : IsIso (f ∣_ U).appTop := (ConcreteCategory.isIso_iff_bijective _).mpr H
  rw [morphismRestrict_appTop] at this
  change IsIso (f.app (U.ι ''ᵁ ⊤) ≫
    X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) at this
  rw [isIso_comp_right_iff] at this
  convert this using 1 <;> rw [U.ι_image_top]

include s hs in
/-- The original map of structure sheaves is an isomorphism by affine locality. -/
lemma structureMap_isIso :
    IsIso (ArtinianProperStructureSheaf.structureMap (q := f)) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : S.affineOpens ↦ U.val)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using S.isBasis_affineOpens)
  intro U
  exact affine_app_isIso f s hs U.val U.property

/-- The actual relative structure-sheaf isomorphism over a locally Noetherian base. -/
def structureSheafIso : S.sheaf ≅
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := by
  let _ := structureMap_isIso f s hs
  exact asIso (ArtinianProperStructureSheaf.structureMap (q := f))

/-- The isomorphism is the original structural pullback on every open. -/
lemma structureSheafIso_hom_app (U : S.Opens) :
    (structureSheafIso f s hs).hom.hom.app (op U) = f.app U := rfl

/-- Actual functions on every inverse-image open are functions from the original base open. -/
def openSectionsIso (U : S.Opens) : Γ(S, U) ≅ Γ(X, f ⁻¹ᵁ U) :=
  ((sheafToPresheaf _ _).mapIso (structureSheafIso f s hs)).app (op U)

/-- The comparison on an arbitrary open retains the original morphism. -/
lemma openSectionsIso_hom (U : S.Opens) : (openSectionsIso f s hs U).hom = f.app U := rfl

include s hs in
/-- Global functions agree without affineness or quasi-compactness of the base. -/
theorem appTop_bijective : Function.Bijective f.appTop :=
  ConcreteCategory.bijective_of_isIso (openSectionsIso f s hs ⊤).hom

end FLT.Mazur.NoetherianProperStructureSheaf
