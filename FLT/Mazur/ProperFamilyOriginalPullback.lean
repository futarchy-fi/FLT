/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyFiberFunctor
public import FLT.Mazur.OriginalFamilyTwistComparison

/-!
# Direct pullback of sections on original test families

The original base twist is pulled along the supplied base map, and the
original section through the explicit tensor and path comparisons. Its full
zero divisor agrees with the independently represented fiber pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open ProperFamilyAtlas FCurve LineSectionBaseChange DualAtlasLineQuotient
open LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "N" => Functor.obj (pushforward q) (Functor.obj (pullback p) L)
local notation "e" => properLineArbitraryBaseChangeIso h L hL hV


local notation "R" => RelativeSection q (Functor.obj (pullback p) L) (hL.pullback p)

local notation "π" => projection M hM

variable {Q U : Scheme.{0}} {p' : Q ⟶ X} {q' : Q ⟶ U} {g' : U ⟶ S}
  (h' : IsPullback p' q' f g') (k : U ⟶ T) (r : Q ⟶ P)
  (hp : r ≫ p = p') (hq : r ≫ q = q' ≫ k) (hg : k ≫ g = g')

include h hV h' hp hq hg
/-- The full pulled zero ideal of the original section is relative Cartier. -/
lemma familySectionPullback_cartier (s : R) :
    RelativeEffectiveCartier q'
      ((lineSectionZeroIdeal (twist_rankOne q _ (hL.pullback p) s.val.baseLine)
        s.val.section_).comap r) := by
  let D := familyFiberPullback h L hL hV h' k hg
    (relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s)
  have he := familyFiberPullback_ideal h L hL hV h' k r hp hq hg
    (relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s)
  exact he ▸ (show RelativeEffectiveCartier q' D.val.val.val from
    ⟨D.val.val.property, D.property⟩)

/-- Pull the original twist and the original section, without divisor reconstruction. -/
def familyPulledTwistedSection (s : R) : TwistedSection q' ((pullback p').obj L) where
  baseLine := pulledBaseLine k s.val.baseLine
  section_ := originalFamilyPullSection k r hp hq L s.val.baseLine s.val.section_
  regular := originalFamilyPullSection_regular k r hp hq L s.val.baseLine hL s.val.section_
    (familySectionPullback_cartier h L hL hV h' k r hp hq hg s).1

/-- The direct original section pullback retains the full ideal. -/
lemma familyPulledTwistedSection_zero (s : R) :
    (TwistedSection.toFiber q' _ (hL.pullback p')
      (familyPulledTwistedSection h L hL hV h' k r hp hq hg s)).val.val =
      (relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s).val.val.val.comap r :=
  originalFamilyPullSection_zero k r hp hq L s.val.baseLine hL s.val.section_
    (familySectionPullback_cartier h L hL hV h' k r hp hq hg s).1

/-- The actual pulled original section remains a relative Cartier section. -/
def familySectionPullback (s : R) :
    RelativeSection q' ((pullback p').obj L) (hL.pullback p') := by
  refine ⟨familyPulledTwistedSection h L hL hV h' k r hp hq hg s, ?_⟩
  change Flat ((TwistedSection.toFiber q' _ (hL.pullback p')
    (familyPulledTwistedSection h L hL hV h' k r hp hq hg s)).val.val.subschemeι ≫ q')
  rw [familyPulledTwistedSection_zero]
  exact (familySectionPullback_cartier h L hL hV h' k r hp hq hg s).2

/-- Independent geometric section pullback agrees with full-divisor pullback. -/
lemma familySectionPullback_toFiber (s : R) :
    relativeSectionToFiber q' _ (hL.pullback p')
        (familySectionPullback h L hL hV h' k r hp hq hg s) =
      familyFiberPullback h L hL hV h' k hg
        (relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (familyPulledTwistedSection_zero h L hL hV h' k r hp hq hg s).trans
    (familyFiberPullback_ideal h L hL hV h' k r hp hq hg
      (relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p) s)).symm

/-- Geometric pullback of the original section precomposes its actual representing morphism. -/
lemma familySectionPullback_toAtlas (s : R) :
    (familySectionPullback h L hL hV h' k r hp hq hg s).toFamilyAtlas h' L hL hV =
      familyAtlasPrecomp L hL hV k hg (s.toFamilyAtlas h L hL hV) := by
  apply (familyAtlasRelativeFiberEquiv h' L hL hV).injective
  rw [familyAtlasRelativeFiberEquiv_toFamilyAtlas, familySectionPullback_toFiber,
    familyAtlasRelativeFiberEquiv_natural, familyAtlasRelativeFiberEquiv_toFamilyAtlas]

end FLT.Mazur.CartierAbel
