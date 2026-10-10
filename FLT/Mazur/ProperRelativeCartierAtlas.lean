/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSplitDirectImageSections
public import FLT.Mazur.DualAtlasLineQuotient

/-!
# Actual projective atlas sections from relative Cartier sections

The ambient bundle is the actual proper direct image. Conversely every
section of its dual projective atlas constructs a relative Cartier section:
the base twist is the dual of its constructed source line. Biduality retains
the original inclusion and proves the geometric round trip.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve SplitLineAffineNeighborhood DualAtlasLineQuotient LineSectionBaseChange
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- Forgetting the choice of twisting dual retains the original line inclusion. -/
def SplitDirectImageSection.toLine (a : SplitDirectImageSection f L) :
    Line ((pushforward f).obj L) :=
  ⟨moduleSheafDual a.baseLine.val, a.baseLine.property.dual, a.map, a.locallySplit⟩

/-- An arbitrary source line supplies a base twist by intrinsic duality. -/
def splitDirectImageOfLine (a : Line ((pushforward f).obj L)) :
    SplitDirectImageSection f L where
  baseLine := ⟨moduleSheafDual a.source, a.rankOne.dual⟩
  map := (lineSheafBidualIso a.rankOne).inv ≫ a.inclusion
  locallySplit := a.locallySplit.precompose a.inclusion (lineSheafBidualIso a.rankOne).symm

/-- The bidual comparison preserves the original ambient inclusion. -/
lemma lineOfSplitDirectImageOfLine (a : Line ((pushforward f).obj L)) :
    (lineSetoid _).r ((splitDirectImageOfLine f L a).toLine f L) a :=
  ⟨(lineSheafBidualIso a.rankOne).symm, rfl⟩

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]
  [GeometricallyIntegral f] [Surjective f] (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))

/-- The actual projective scheme sections of the proved locally free direct image. -/
abbrev DirectImageAtlasSection := Section ((pushforward f).obj L)
  (properLinePushforward_locallyFiniteFree f L hL hV)

/-- The atlas section of a relative Cartier section and its original twisting line. -/
def RelativeSection.toAtlas (s : RelativeSection f L hL) :
    DirectImageAtlasSection f L hL hV :=
  toSection _ _ ((s.toSplitDirectImage f L hL hV).toLine f L)

/-- Recover a relative Cartier section from the actual forward line of an atlas section. -/
def relativeSectionOfAtlas (p : DirectImageAtlasSection f L hL hV) :
    RelativeSection f L hL :=
  (splitDirectImageOfLine f L (fromSection _ _ p)).toRelative f L hL hV

/-- Geometric reconstruction recovers the original projective atlas section. -/
lemma toAtlas_relativeSectionOfAtlas (p : DirectImageAtlasSection f L hL hV) :
    (relativeSectionOfAtlas f L hL hV p).toAtlas f L hL hV = p := by
  change toSection _ _ (((splitDirectImageOfLine f L (fromSection _ _ p)).toRelative
    f L hL hV).toSplitDirectImage f L hL hV |>.toLine f L) = p
  rw [toSplitDirectImage_toRelative]
  exact ((toSection_eq_iff _ _ _ _).mpr
    (lineOfSplitDirectImageOfLine f L (fromSection _ _ p))).trans
      (toSection_fromSection _ _ p)

/-- Every actual atlas section is represented by an original relative Cartier section. -/
theorem relativeSection_toAtlas_surjective :
    Function.Surjective (RelativeSection.toAtlas f L hL hV) :=
  fun p ↦ ⟨relativeSectionOfAtlas f L hL hV p, toAtlas_relativeSectionOfAtlas f L hL hV p⟩

end FLT.Mazur.CartierAbel
