/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRelativeCartierAtlas

/-!
# Retained line projections of original Cartier sections

Factor the line record through the original twisted section. This lets later
base-change comparisons rewrite the section before inspecting its dependent
line and inclusion fields.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SplitLineAffineNeighborhood DualAtlasLineQuotient
attribute [local irreducible] twistedSectionPushforwardEquiv ModuleSheafTensor.tensor
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- Retain the original dual twisting line and its given split direct-image map. -/
def TwistedSection.retainedLine (s : TwistedSection f L)
    (hs : LocallySplit (s.toDirectImage f L).map) : Line ((pushforward f).obj L) :=
  ⟨moduleSheafDual s.baseLine.val, s.baseLine.property.dual,
    (s.toDirectImage f L).map, hs⟩

/-- Equality of original twisted sections identifies their retained lines. -/
lemma TwistedSection.retainedLine_congr (s t : TwistedSection f L)
    (hs : LocallySplit (s.toDirectImage f L).map)
    (ht : LocallySplit (t.toDirectImage f L).map) (h : s = t) :
    s.retainedLine f L hs = t.retainedLine f L ht := by
  subst t
  rfl

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]
  [Surjective f] (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))

/-- Forgetting the split-section record retains exactly the original twisted section. -/
lemma RelativeSection.toLine_eq_retainedLine (s : RelativeSection f L hL) :
    (s.toSplitDirectImage f L hL hV).toLine f L =
      s.val.retainedLine f L
        (relativeSection_proper_directImage_locallySplit f L hL hV s) := rfl

/-- Replace the original twisted section before comparing its dependent line fields. -/
lemma RelativeSection.toLine_eq_of_val (s : RelativeSection f L hL)
    (t : TwistedSection f L) (ht : LocallySplit (t.toDirectImage f L).map)
    (h : s.val = t) :
    (s.toSplitDirectImage f L hL hV).toLine f L = t.retainedLine f L ht :=
  (s.toLine_eq_retainedLine f L hL hV).trans
    (TwistedSection.retainedLine_congr f L s.val t _ ht h)

end FLT.Mazur.CartierAbel
