/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankOneAmbientLineClassification
public import FLT.Mazur.ProperRelativeCartierAtlas

/-!
# The normalized section of a rank-one direct image

The entire direct image supplies a canonical retained line. Its dual is
the base twist, and inverse biduality is the actual section map. No choice
of generator or trivialization enters this construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  (hN : LocallyFreeRankOne ((pushforward f).obj L))

/-- The original direct image, normalized by its intrinsic dual and biduality. -/
@[irreducible] def rankOneSplitSection : SplitDirectImageSection f L :=
  { baseLine := ⟨moduleSheafDual ((pushforward f).obj L), hN.dual⟩
    map := (lineSheafBidualIso hN).inv
    locallySplit := fun _ ↦ ⟨⊤, trivial, inferInstance⟩ }

/-- The twisting line is precisely the dual of the actual direct image. -/
lemma rankOneSplitSection_baseLine :
    (rankOneSplitSection f L hN).baseLine.val = moduleSheafDual ((pushforward f).obj L) := by
  unfold rankOneSplitSection
  rfl

/-- The normalized section map is inverse biduality of the actual direct image. -/
lemma rankOneSplitSection_map :
    HEq (rankOneSplitSection f L hN).map (lineSheafBidualIso hN).inv := by
  unfold rankOneSplitSection
  rfl

/-- The normalized original section map is an isomorphism, before taking a zero ideal. -/
theorem rankOneSplitSection_isIso : IsIso (rankOneSplitSection f L hN).map := by
  exact (rankOneSplitSection f L hN).locallySplit.isIso _
    (rankOneSplitSection f L hN).baseLine.property.dual hN

end FLT.Mazur.CartierAbel
