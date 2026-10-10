/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyUniversalLineRecovery
public import FLT.Mazur.RetainedLineTwistedSection

/-!
# Twisted-section recovery on the original proper test family

The proved source isomorphism identifies the normalized recovered line's
actual tensor section with the original retained line's tensor section.
Their full zero ideals agree without Noetherian hypotheses on the test base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperFamilyAtlas
open FCurve CartierAbel LineSectionBaseChange DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (b : Line ((pushforward q).obj ((pullback p).obj L)))

/-- Source recovery induces the actual contravariant identification of twisting lines. -/
def recoveredTwistIso : moduleSheafDual b.source ≅
    moduleSheafDual (recoveredLine h L hL hV b).source :=
  moduleSheafDualIso _ (recoveryIso h L hL hV b)

/-- The original tensor section agrees with the recovered one through the retained twist. -/
lemma recoveredSection_eq :
    (ModuleSheafTensor.map (𝟙 ((pullback p).obj L))
      ((pullback q).map (recoveredTwistIso h L hL hV b).hom)).app ⊤
        (retainedLineSection q ((pullback p).obj L) b) =
      retainedLineSection q ((pullback p).obj L) (recoveredLine h L hL hV b) :=
  retainedLineSection_sourceIso q _ _ b (recoveryIso h L hL hV b)
    (recoveryIso_inclusion h L hL hV b)

/-- Recovery preserves every equation of the original section's full zero subscheme. -/
lemma recoveredSection_zeroIdeal :
    lineSectionZeroIdeal ((hL.pullback p).tensor (b.rankOne.dual.pullback q))
        (retainedLineSection q ((pullback p).obj L) b) =
      lineSectionZeroIdeal ((hL.pullback p).tensor
        ((recoveredLine h L hL hV b).rankOne.dual.pullback q))
        (retainedLineSection q ((pullback p).obj L) (recoveredLine h L hL hV b)) :=
  retainedLineSection_zeroIdeal q _ (hL.pullback p) _ b (recoveryIso h L hL hV b)
    (recoveryIso_inclusion h L hL hV b)

end FLT.Mazur.ProperFamilyAtlas
