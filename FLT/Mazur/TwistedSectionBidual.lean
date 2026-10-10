/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafBidualTriangle
public import FLT.Mazur.TwistedSectionBaseLineNaturality

/-!
# Bidual transport of an original tensor section

The raw direct-image correspondence respects canonical biduality before
converting the section into a retained line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
  lineSheafBidualIso moduleSheafDualMap
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  {B : S.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))

/-- The direct-image map of the bidual tensor section is inverse bidual transport. -/
lemma twistedSectionPushforwardEquiv_bidual :
    twistedSectionPushforwardEquiv f L hB.dual.dual
        ((map (𝟙 L) ((pullback f).map (lineSheafBidualIso hB).hom)).app ⊤ s) =
      (lineSheafBidualIso hB.dual).inv ≫ twistedSectionPushforwardEquiv f L hB s := by
  rw [twistedSectionPushforwardEquiv_baseLineIso,
    ← lineSheafBidual_dual_inv]

/-- Inverse direct-image correspondence recovers the original bidual tensor section. -/
lemma twistedSectionPushforwardEquiv_bidual_symm :
    (twistedSectionPushforwardEquiv f L hB.dual.dual).symm
        ((lineSheafBidualIso hB.dual).inv ≫ twistedSectionPushforwardEquiv f L hB s) =
      (map (𝟙 L) ((pullback f).map (lineSheafBidualIso hB).hom)).app ⊤ s := by
  rw [← twistedSectionPushforwardEquiv_bidual, Equiv.symm_apply_apply]

end FLT.Mazur.CartierAbel
