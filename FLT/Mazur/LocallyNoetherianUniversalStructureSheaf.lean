/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianUniversalStructureSheaf

/-!
# Universal structure-sheaf comparison over locally Noetherian bases

Affine pieces of an arbitrary changed base can be chosen inside inverse
images of affine opens of the original base. Comparison on this basis gives
the actual structure-sheaf isomorphism without global affineness or compactness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace FLT.Mazur.LocallyNoetherianUniversalStructureSheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  [IsLocallyNoetherian S]
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]

include h s hs in
/-- The structural map is invertible on each affine piece mapping into an affine base open. -/
lemma affine_piece_isIso (V : S.Opens) (hV : IsAffineOpen V)
    (W : T.Opens) (hW : IsAffineOpen W) (hWV : W ≤ g ⁻¹ᵁ V) : IsIso (q.app W) := by
  let _ : IsAffine V.toScheme := hV
  let _ : IsAffine W.toScheme := hW
  let _ : IsNoetherianRing Γ(V.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hle : q ⁻¹ᵁ W ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact q.preimage_mono hWV
  have H : IsPullback (p.resLE (f ⁻¹ᵁ V) (q ⁻¹ᵁ W) hle)
      (q ∣_ W) (f ∣_ V) (g.resLE V W hWV) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE h hWV (le_rfl : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V)
        (inf_eq_right.mpr hle).symm
  let hv := (isPullback_morphismRestrict f V).flip
  have hb := NoetherianProperAffineBaseChange.appTop_bijective H
    (ArtinianProperAffineBaseChange.sectionOfSquare hv s hs)
    (ArtinianProperAffineBaseChange.sectionOfSquare_projection hv s hs)
  have : IsIso (q ∣_ W).appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hb
  rw [morphismRestrict_appTop] at this
  change IsIso (q.app (W.ι ''ᵁ ⊤) ≫
    P.presheaf.map (eqToHom (image_morphismRestrict_preimage q W ⊤)).op) at this
  rw [isIso_comp_right_iff] at this
  convert this using 1 <;> rw [W.ι_image_top]

/-- Affine opens of the new base subordinate to affine opens of the original base. -/
abbrev AffinePiece (g : T ⟶ S) :=
  Σ V : S.affineOpens, {W : T.affineOpens // W.val ≤ g ⁻¹ᵁ V.val}

omit [IsLocallyNoetherian S] in
/-- These subordinate affine opens form a basis on any changed base. -/
lemma affinePiece_isBasis (g : T ⟶ S) :
    Opens.IsBasis (Set.range (fun U : AffinePiece g ↦ U.2.1.val)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨V, hV, hxV, _⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show g x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show x ∈ W ⊓ g ⁻¹ᵁ V from ⟨hx, hxV⟩)
  exact ⟨U, ⟨⟨⟨V, hV⟩, ⟨⟨U, hU⟩, hUW.trans inf_le_right⟩⟩, rfl⟩,
    hxU, hUW.trans inf_le_left⟩

include h s hs in
/-- The original structure-sheaf map is invertible after every scheme base change. -/
lemma structureMap_isIso : IsIso (ArtinianProperStructureSheaf.structureMap (q := q)) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis (affinePiece_isBasis g)
  intro U
  exact affine_piece_isIso h s hs U.1.val U.1.property U.2.1.val U.2.1.property U.2.2

/-- Universal comparison of the actual structure sheaves over a locally Noetherian base. -/
def structureSheafIso : T.sheaf ≅
    (TopCat.Sheaf.pushforward CommRingCat q.base).obj P.sheaf := by
  let _ := structureMap_isIso h s hs
  exact asIso (ArtinianProperStructureSheaf.structureMap (q := q))

/-- The sheaf comparison retains the original structure morphism on every open. -/
lemma structureSheafIso_hom_app (U : T.Opens) :
    (structureSheafIso h s hs).hom.hom.app (op U) = q.app U := rfl

/-- Actual sections on each open of an arbitrary changed base. -/
def openSectionsIso (U : T.Opens) : Γ(T, U) ≅ Γ(P, q ⁻¹ᵁ U) :=
  ((sheafToPresheaf _ _).mapIso (structureSheafIso h s hs)).app (op U)

/-- The open comparison is the original structural pullback. -/
lemma openSectionsIso_hom (U : T.Opens) : (openSectionsIso h s hs U).hom = q.app U := rfl

include h s hs in
/-- Global functions commute with arbitrary base change of a locally Noetherian family. -/
lemma appTop_bijective : Function.Bijective q.appTop :=
  ConcreteCategory.bijective_of_isIso (openSectionsIso h s hs ⊤).hom

end FLT.Mazur.LocallyNoetherianUniversalStructureSheaf
