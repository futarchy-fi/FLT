/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRelativeCartierAtlas
public import FLT.Mazur.TwistedSectionBaseLineNaturality
public import FLT.Mazur.LineSectionZeroIdealOrbits

/-!
# Original twisted sections from retained direct-image lines

Intrinsic biduality defines the section without regularity hypotheses.
An isomorphism of retained sources preserving their inclusions transports
the actual tensor sections through its contravariant dual.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- The original tensor section corresponding to a retained direct-image inclusion. -/
@[irreducible] def retainedLineSection (a : Line ((pushforward f).obj L)) :
    Γ(tensor L ((pullback f).obj (moduleSheafDual a.source)), ⊤) :=
  (twistedSectionPushforwardEquiv f L a.rankOne.dual).symm
    ((lineSheafBidualIso a.rankOne).inv ≫ a.inclusion)

/-- Biduality specifies the original direct-image map of the constructed section. -/
lemma retainedLineSection_map (a : Line ((pushforward f).obj L)) :
    twistedSectionPushforwardEquiv f L a.rankOne.dual (retainedLineSection f L a) =
      (lineSheafBidualIso a.rankOne).inv ≫ a.inclusion := by
  unfold retainedLineSection
  exact Equiv.apply_symm_apply _ _

/-- Inverse canonical biduality is natural on the original sheaf maps. -/
lemma lineBidual_inv_naturality {A B : S.Modules}
    (hA : LocallyFreeRankOne A) (hB : LocallyFreeRankOne B) (k : A ⟶ B) :
    moduleSheafDualMap (moduleSheafDual B) (moduleSheafDualMap A k) ≫
        (lineSheafBidualIso hB).inv = (lineSheafBidualIso hA).inv ≫ k := by
  apply (cancel_epi (lineSheafBidualIso hA).hom).mp
  rw [Iso.hom_inv_id_assoc]
  change moduleSheafBidual A ≫ _ ≫ _ = k
  rw [← Category.assoc, moduleSheafBidual_naturality, Category.assoc]
  change k ≫ (lineSheafBidualIso hB).hom ≫ (lineSheafBidualIso hB).inv = k
  rw [Iso.hom_inv_id, Category.comp_id]

/-- A retained-source isomorphism transports the original tensor sections. -/
lemma retainedLineSection_sourceIso (a b : Line ((pushforward f).obj L))
    (e : a.source ≅ b.source) (he : e.hom ≫ b.inclusion = a.inclusion) :
    (map (𝟙 L) ((pullback f).map (moduleSheafDualIso a.source e).hom)).app ⊤
        (retainedLineSection f L b) = retainedLineSection f L a := by
  apply (twistedSectionPushforwardEquiv f L a.rankOne.dual).injective
  rw [twistedSectionPushforwardEquiv_baseLineIso f L
    (moduleSheafDualIso a.source e) b.rankOne.dual a.rankOne.dual,
    retainedLineSection_map, retainedLineSection_map]
  change moduleSheafDualMap (moduleSheafDual b.source)
    (moduleSheafDualMap a.source e.hom) ≫ _ ≫ _ = _
  rw [← Category.assoc, lineBidual_inv_naturality, Category.assoc, he]

/-- Retained-source transport preserves the full zero ideal, including multiplicities. -/
lemma retainedLineSection_zeroIdeal (hL : LocallyFreeRankOne L)
    (a b : Line ((pushforward f).obj L)) (e : a.source ≅ b.source)
    (he : e.hom ≫ b.inclusion = a.inclusion) :
    lineSectionZeroIdeal (hL.tensor (b.rankOne.dual.pullback f))
        (retainedLineSection f L b) =
      lineSectionZeroIdeal (hL.tensor (a.rankOne.dual.pullback f))
        (retainedLineSection f L a) :=
  lineSectionZeroIdeal_eq_of_iso _ _
    (congr (Iso.refl L) ((pullback f).mapIso (moduleSheafDualIso a.source e))) _ _
    (retainedLineSection_sourceIso f L a b e he)

end FLT.Mazur.CartierAbel
