/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyAtlasRecovery

/-!
# The original proper test family is the pullback of the atlas family

The total-space map is constructed from the original square. Its cartesian
property gives an actual isomorphism to the universal-family fiber product.
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
local notation "π" => projection M hM
local notation "a" => morphism h L hL hV b

/-- The original total space maps to the actual universal family over the atlas. -/
def familyMap : P ⟶ Limits.pullback f π :=
  Limits.pullback.lift p (q ≫ a) (by rw [Category.assoc, morphism_projection, h.w])

/-- The family map retains the original morphism into the original total space. -/
lemma familyMap_fst : familyMap h L hL hV b ≫ Limits.pullback.fst f π = p :=
  Limits.pullback.lift_fst _ _ _

/-- The family map lies over the original line's atlas morphism. -/
lemma familyMap_snd : familyMap h L hL hV b ≫ Limits.pullback.snd f π = q ≫ a :=
  Limits.pullback.lift_snd _ _ _

/-- The independently specified original family is cartesian over the universal family. -/
lemma familyMap_isPullback :
    IsPullback (familyMap h L hL hV b) q (Limits.pullback.snd f π) a := by
  apply IsPullback.of_right (h₁₂ := Limits.pullback.fst f π) (h₂₂ := π)
  · simpa only [familyMap_fst, morphism_projection] using h
  · exact familyMap_snd h L hL hV b
  · exact IsPullback.of_hasPullback f π

/-- The actual fiber-product identification, constructed from the original square. -/
def familyIso : P ≅ Limits.pullback (Limits.pullback.snd f π) a :=
  (familyMap_isPullback h L hL hV b).isoPullback

/-- The identification preserves the original universal-family map. -/
lemma familyIso_fst :
    (familyIso h L hL hV b).hom ≫ Limits.pullback.fst _ _ = familyMap h L hL hV b :=
  (familyMap_isPullback h L hL hV b).isoPullback_hom_fst

/-- The identification preserves the original family projection. -/
lemma familyIso_snd : (familyIso h L hL hV b).hom ≫ Limits.pullback.snd _ _ = q :=
  (familyMap_isPullback h L hL hV b).isoPullback_hom_snd

end FLT.Mazur.ProperFamilyAtlas
