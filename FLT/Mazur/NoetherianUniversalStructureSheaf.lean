/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianProperStructureSheaf
public import FLT.Mazur.NoetherianProperAffineBaseChange

/-!
# Universal structure-sheaf comparison over a Noetherian affine base

After an arbitrary scheme base change, the original structural map is an
isomorphism on an affine basis. Sheaf locality gives the actual comparison on
every open, without reducedness, Noetherianity, or affineness of the new base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.NoetherianUniversalStructureSheaf
open ArtinianProperStructureSheaf (structureMap)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]

include h s hs in
/-- Structural pullback is invertible on every affine open of the arbitrary changed base. -/
lemma affine_app_isIso (U : T.Opens) (hU : IsAffineOpen U) : IsIso (q.app U) := by
  let _ : IsAffine U.toScheme := hU
  have H := NoetherianProperAffineBaseChange.appTop_bijective
    ((isPullback_morphismRestrict q U).flip.paste_horiz h) s hs
  have : IsIso (q ∣_ U).appTop := (ConcreteCategory.isIso_iff_bijective _).mpr H
  rw [morphismRestrict_appTop] at this
  change IsIso (q.app (U.ι ''ᵁ ⊤) ≫
    P.presheaf.map (eqToHom (image_morphismRestrict_preimage q U ⊤)).op) at this
  rw [isIso_comp_right_iff] at this
  convert this using 1 <;> rw [U.ι_image_top]

include h s hs in
/-- Invertibility on the affine basis gives invertibility of the actual sheaf map. -/
lemma structureMap_isIso : IsIso (structureMap (q := q)) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : T.affineOpens ↦ U.val)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using T.isBasis_affineOpens)
  intro U
  exact affine_app_isIso h s hs U.val U.property

/-- The actual universal relative structure-sheaf isomorphism. -/
def structureSheafIso : T.sheaf ≅
    (TopCat.Sheaf.pushforward CommRingCat q.base).obj P.sheaf := by
  let _ := structureMap_isIso h s hs
  exact asIso (structureMap (q := q))

/-- On every open, the isomorphism retains the original structural pullback. -/
lemma structureSheafIso_hom_app (U : T.Opens) :
    (structureSheafIso h s hs).hom.hom.app (op U) = q.app U := rfl

/-- The actual comparison of functions on each open of the arbitrary changed base. -/
def openSectionsIso (U : T.Opens) : Γ(T, U) ≅ Γ(P, q ⁻¹ᵁ U) :=
  ((sheafToPresheaf _ _).mapIso (structureSheafIso h s hs)).app (op U)

/-- The open comparison is the original pullback on functions. -/
lemma openSectionsIso_hom (U : T.Opens) : (openSectionsIso h s hs U).hom = q.app U := rfl

include h s hs in
/-- Global functions commute with every scheme base change of the Noetherian family. -/
lemma appTop_bijective : Function.Bijective q.appTop :=
  ConcreteCategory.bijective_of_isIso (openSectionsIso h s hs ⊤).hom

end FLT.Mazur.NoetherianUniversalStructureSheaf
