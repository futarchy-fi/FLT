/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperUniversalDirectImageLine
public import FLT.Mazur.DualAtlasUniversalLineRecovery

/-!
# The atlas map and retained source for an original proper test family

The original base-change mate transports a test-family line to the atlas.
Pulling the universal source along this map recovers the original source,
with the actual mate and the specified base map in the inclusion equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperFamilyAtlas
open FCurve LineSectionBaseChange DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (b : Line ((pushforward q).obj ((pullback p).obj L)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "e" => properLineArbitraryBaseChangeIso h L hL hV

/-- Normalize the original retained line using the inverse of the actual proper mate. -/
def normalizedLine : Line ((pullback g).obj M) := b.changeAmbient (e).symm

/-- The atlas map of an independently specified original proper test-family line. -/
def morphism : T ⟶ space M hM :=
  DualAtlasUniversalLine.lineMorphism M hM g (normalizedLine h L hL hV b)

/-- The atlas map retains the original test-base morphism. -/
lemma morphism_projection : morphism h L hL hV b ≫ projection M hM = g :=
  DualAtlasUniversalLine.lineMorphism_projection M hM g (normalizedLine h L hL hV b)

/-- Universal-source recovery for the original proper direct-image line. -/
@[irreducible] def sourceIso :
    (pullback (morphism h L hL hV b)).obj
      (DualAtlasUniversalLine.universalLine M hM).source ≅ b.source :=
  DualAtlasUniversalLine.recoveryIso M hM g (normalizedLine h L hL hV b)

/-- Source recovery retains the original mate and original inclusion on the test family. -/
lemma sourceIso_inclusion :
    (sourceIso h L hL hV b).hom ≫ b.inclusion =
      (pullback (morphism h L hL hV b)).map
          (DualAtlasUniversalLine.universalLine M hM).inclusion ≫
        (SheafPullbackPathComparison.comparison (morphism h L hL hV b)
          (projection M hM) g (morphism_projection h L hL hV b)).hom.app M ≫
            DirectImageBaseChange.comparison p q f g h.w.symm L := by
  have hh := congrArg (fun k ↦ k ≫ (e).hom)
    (DualAtlasUniversalLine.recoveryIso_inclusion M hM g (normalizedLine h L hL hV b))
  simp only [normalizedLine, Line.changeAmbient, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  simpa only [sourceIso, morphism, normalizedLine, Line.changeAmbient, Iso.symm_hom,
    properLineArbitraryBaseChangeIso_hom] using hh

end FLT.Mazur.ProperFamilyAtlas
