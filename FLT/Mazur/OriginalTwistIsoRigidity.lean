/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTwistOrbitRelation
public import FLT.Mazur.LocallySplitSheafMonomorphism

/-!
# Rigidity of original section-preserving twisting-line comparisons

The actual direct-image map is locally split. Cancellation of that map and
biduality make a section-preserving isomorphism of original base twists unique.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- Duality is injective on morphisms between actual line bundles. -/
lemma originalLine_dual_injective {B C : S.Modules} (hC : LocallyFreeRankOne C)
    (a b : B ⟶ C) (hab : moduleSheafDualMap B a = moduleSheafDualMap B b) : a = b := by
  apply (cancel_mono (lineSheafBidualIso hC).hom).mp
  change a ≫ moduleSheafBidual C = b ≫ moduleSheafBidual C
  rw [← moduleSheafBidual_naturality, ← moduleSheafBidual_naturality, hab]

/-- The original section determines its original base-line comparison uniquely. -/
lemma originalTwistIso_unique (s t : TwistedSection f L)
    (hs : SplitLineAffineNeighborhood.LocallySplit (s.toDirectImage f L).map)
    (e d : s.baseLine.val ≅ t.baseLine.val)
    (he : (map (𝟙 L) ((pullback f).map e.hom)).app ⊤ s.section_ = t.section_)
    (hd : (map (𝟙 L) ((pullback f).map d.hom)).app ⊤ s.section_ = t.section_) : e = d := by
  let _ := hs.mono
  apply Iso.ext
  apply originalLine_dual_injective t.baseLine.property
  apply (cancel_mono (s.toDirectImage f L).map).mp
  have he' := twistedSectionPushforwardEquiv_baseLineIso f L e
    s.baseLine.property t.baseLine.property s.section_
  have hd' := twistedSectionPushforwardEquiv_baseLineIso f L d
    s.baseLine.property t.baseLine.property s.section_
  rw [he] at he'
  rw [hd] at hd'
  exact he'.symm.trans hd'

end FLT.Mazur.CartierAbel
