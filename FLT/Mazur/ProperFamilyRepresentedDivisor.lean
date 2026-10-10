/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyAbelRepresentation

/-!
# The representing equivalence is actual universal-divisor pullback

Each original atlas morphism gives an independently constructed map of total
spaces. The represented divisor is the full comap of the universal ideal,
including multiplicities, along this map of the original test family.
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

/-- The map from the original total space determined by an actual atlas morphism. -/
def atlasFamilyMap (a : TestMorphism L hL hV (g := g)) : P ⟶ Limits.pullback f π :=
  Limits.pullback.lift p (q ≫ a.val) (by rw [Category.assoc, a.property, h.w])

omit [GeometricallyIntegral f] in
/-- The total-space map retains the original projection into the original family. -/
lemma atlasFamilyMap_fst (a : TestMorphism L hL hV (g := g)) :
    atlasFamilyMap h L hL hV a ≫ Limits.pullback.fst f π = p :=
  Limits.pullback.lift_fst _ _ _

omit [GeometricallyIntegral f] in
/-- The total-space map lies over the independently specified original atlas morphism. -/
lemma atlasFamilyMap_snd (a : TestMorphism L hL hV (g := g)) :
    atlasFamilyMap h L hL hV a ≫ Limits.pullback.snd f π = q ≫ a.val :=
  Limits.pullback.lift_snd _ _ _

omit [GeometricallyIntegral f] in
/-- Each original atlas morphism identifies the original test family as a cartesian pullback. -/
lemma atlasFamilyMap_isPullback (a : TestMorphism L hL hV (g := g)) :
    IsPullback (atlasFamilyMap h L hL hV a) q (Limits.pullback.snd f π) a.val := by
  apply IsPullback.of_right (h₁₂ := Limits.pullback.fst f π) (h₂₂ := π)
  · simpa only [atlasFamilyMap_fst, a.property] using h
  · exact atlasFamilyMap_snd h L hL hV a
  · exact IsPullback.of_hasPullback f π

/-- On an original section, the independently constructed total-space maps agree. -/
lemma atlasFamilyMap_toFamilyAtlas (s : R) :
    atlasFamilyMap h L hL hV (s.toFamilyAtlas h L hL hV) =
      familyMap h L hL hV (s.familyLine h L hL hV) := rfl

/-- The representing equivalence preserves the full zero ideal of each original section. -/
lemma familyAtlasRelativeFiberEquiv_section_ideal (s : R) :
    (familyAtlasRelativeFiberEquiv h L hL hV (s.toFamilyAtlas h L hL hV)).val.val.val =
      (ProperUniversalDirectImage.universalIdeal f L hL hV).comap
        (atlasFamilyMap h L hL hV (s.toFamilyAtlas h L hL hV)) := by
  rw [familyAtlasRelativeFiberEquiv_toFamilyAtlas, atlasFamilyMap_toFamilyAtlas]
  have he := congrArg (fun b : Line N ↦
    (ProperUniversalDirectImage.universalIdeal f L hL hV).comap
      (familyMap h L hL hV b)) (familyLine_eq_original h L hL hV s)
  exact (ProperFamilyAtlas.originalSection_zeroIdeal h L hL hV s.val.baseLine
    s.val.section_ (familyOriginalSection_locallySplit h L hL hV s)).trans he.symm

/-- Every represented divisor is the full geometric pullback of the universal divisor. -/
theorem familyAtlasRelativeFiberEquiv_ideal (a : TestMorphism L hL hV (g := g)) :
    (familyAtlasRelativeFiberEquiv h L hL hV a).val.val.val =
      (ProperUniversalDirectImage.universalIdeal f L hL hV).comap
        (atlasFamilyMap h L hL hV a) := by
  have he := familyAtlasRelativeFiberEquiv_section_ideal h L hL hV
    (familySectionOfAtlas h L hL hV a)
  simpa only [toFamilyAtlas_familySectionOfAtlas] using he

/-- The full original divisor recovers its actual atlas morphism, independently of its section. -/
lemma familyAtlasRelativeFiberEquiv_symm_ideal
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    D.val.val.val = (ProperUniversalDirectImage.universalIdeal f L hL hV).comap
      (atlasFamilyMap h L hL hV ((familyAtlasRelativeFiberEquiv h L hL hV).symm D)) := by
  have he := familyAtlasRelativeFiberEquiv_ideal h L hL hV
    ((familyAtlasRelativeFiberEquiv h L hL hV).symm D)
  simpa only [Equiv.apply_symm_apply] using he

end FLT.Mazur.CartierAbel
