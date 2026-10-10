/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRepresentedDivisor

/-!
# Naturality of the represented full divisor on original test families

Precomposition of actual atlas morphisms pulls the represented divisor along
the actual map of total spaces. The comparison is equality of full ideals,
without choices of sections, frames or twisting-line representatives.
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

/-- Precompose the actual representing morphism along its independently supplied base map. -/
def familyAtlasPrecomp (a : TestMorphism L hL hV (g := g)) :
    TestMorphism L hL hV (g := g') :=
  ⟨k ≫ a.val, by rw [Category.assoc, a.property, hg]⟩

omit [GeometricallyIntegral f] in
include hp hq in
/-- Precomposition retains the actual original map between the total spaces. -/
lemma atlasFamilyMap_precomp (a : TestMorphism L hL hV (g := g)) :
    atlasFamilyMap h' L hL hV (familyAtlasPrecomp L hL hV k hg a) =
      r ≫ atlasFamilyMap h L hL hV a := by
  apply Limits.pullback.hom_ext
  · rw [atlasFamilyMap_fst, Category.assoc, atlasFamilyMap_fst]
    exact hp.symm
  · rw [atlasFamilyMap_snd, Category.assoc, atlasFamilyMap_snd]
    change q' ≫ (k ≫ a.val) = r ≫ (q ≫ a.val)
    rw [← Category.assoc r q, hq, Category.assoc]

include hp hq in
/-- The represented full relative divisor pulls back along the actual map of original families. -/
theorem familyAtlasRelativeFiberEquiv_natural_ideal
    (a : TestMorphism L hL hV (g := g)) :
    (familyAtlasRelativeFiberEquiv h' L hL hV
        (familyAtlasPrecomp L hL hV k hg a)).val.val.val =
      (familyAtlasRelativeFiberEquiv h L hL hV a).val.val.val.comap r := by
  rw [familyAtlasRelativeFiberEquiv_ideal, familyAtlasRelativeFiberEquiv_ideal,
    atlasFamilyMap_precomp h L hL hV h' k r hp hq hg]
  exact Scheme.IdealSheafData.comap_comp _ _ _

end FLT.Mazur.CartierAbel
