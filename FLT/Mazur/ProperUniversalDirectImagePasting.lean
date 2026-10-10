/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperUniversalDirectImageLine
public import FLT.Mazur.ProperLineIteratedArbitraryBaseChange

/-!
# Iterated transport of the actual universal direct-image line

The actual second base-change mate transports the pulled original universal
line. Pasting identifies its normalized inclusion with the composite mate.
Neither changed base is required to be affine or Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "π" => projection M hM
local notation "p" => Limits.pullback.fst f π
local notation "q" => Limits.pullback.snd f π


/-- Pull the original universal direct-image line through the actual second mate. -/
@[irreducible] def iteratedLine {T Q : Scheme.{0}} (a : T ⟶ space M hM)
    (r : Q ⟶ Limits.pullback f π) (t : Q ⟶ T) (h : IsPullback r t q a) :
    Line ((pushforward t).obj ((pullback r).obj
    ((pullback p).obj L))) :=
  ((line f L hL hV).baseChange a).changeAmbient
    (properLineIteratedBaseChangeIso (IsPullback.of_hasPullback f π) L hL hV h)

/-- Pasting the mates retains the original universal inclusion and coefficient comparison. -/
lemma iteratedLine_paste {T Q : Scheme.{0}} (a : T ⟶ space M hM)
    (r : Q ⟶ Limits.pullback f π) (t : Q ⟶ T) (h : IsPullback r t q a) :
    (iteratedLine f L hL hV a r t h).changeAmbient
        ((pushforward t).mapIso ((pullbackComp r p).app L)) =
      ((DualAtlasUniversalLine.universalLine M hM).baseChange a).changeAmbient
        ((pullbackComp a π).app M ≪≫
          properLineArbitraryBaseChangeIso (h.paste_horiz (IsPullback.of_hasPullback f π))
            L hL hV) := by
  unfold iteratedLine line
  simp only [Line.baseChange, Line.changeAmbient, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, properLineIteratedBaseChangeIso_hom,
    properLineArbitraryBaseChangeIso_hom]
  congr 1
  rw [DirectImageBaseChange.comparison_paste]

end FLT.Mazur.ProperUniversalDirectImage
