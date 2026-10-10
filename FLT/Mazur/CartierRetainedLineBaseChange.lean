/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierRetainedLineProjections
public import FLT.Mazur.DualAtlasSectionTransport

/-!
# Base-change comparisons for retained Cartier line records

An isomorphism of the original dual twisting lines preserving their maps
supplies the retained-line relation. The splitting witnesses remain abstract,
so applying this comparison does not expand their geometric constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SplitLineAffineNeighborhood DualAtlasLineQuotient
attribute [local irreducible] twistedSectionPushforwardEquiv ModuleSheafTensor.tensor
variable {X S Y T : Scheme.{0}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S)
  (L : X.Modules) (N : Y.Modules)

/-- Compare retained lines using only their original dual-line maps. -/
lemma TwistedSection.retainedLine_baseChange_relation
    (s : TwistedSection f L) (t : TwistedSection q N)
    (hs : LocallySplit (s.toDirectImage f L).map)
    (ht : LocallySplit (t.toDirectImage q N).map)
    (e : (pullback g).obj ((pushforward f).obj L) ≅ (pushforward q).obj N)
    (d : (pullback g).obj (moduleSheafDual s.baseLine.val) ≅
      moduleSheafDual t.baseLine.val)
    (hd : d.hom ≫ (t.toDirectImage q N).map =
      (pullback g).map (s.toDirectImage f L).map ≫ e.hom) :
    (lineSetoid ((pushforward q).obj N)).r
      (((s.retainedLine f L hs).baseChange g).changeAmbient e)
      (t.retainedLine q N ht) :=
  ⟨d, hd⟩

variable (hL : LocallyFreeRankOne L)

/-- The relative pullback record retains the independently pulled twisted section. -/
lemma relativeSectionBaseChange_val (s : RelativeSection f L hL) :
    (relativeSectionBaseChange f g L hL s).val = pulledTwistedSection f g L hL s := rfl

end FLT.Mazur.CartierAbel
