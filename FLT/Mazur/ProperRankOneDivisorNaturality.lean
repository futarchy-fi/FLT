/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperRankOneNormalizedDivisor
public import FLT.Mazur.ProperFamilyDivisorNaturality

/-!
# The normalized rank-one divisor is natural as a full ideal

The original atlas equivalence identifies the constructed normalized divisor
with a geometric pullback of the universal ideal. Uniqueness proves that
these full ideals pull back along every map of original test families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange ProperFamilyAtlas LocallyFreeDualProjectiveAtlas
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
  LocallyFreeDualProjectiveAtlas.projection
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)))

/-- The actual atlas map of the intrinsic normalized divisor. -/
def rankOneFamilyAtlas : TestMorphism L hL hV (g := g) :=
  (familyAtlasRelativeFiberEquiv h L hL hV).symm (rankOneFamilyDivisor h L hL hV hN)

/-- The map recovers the entire constructed normalized divisor. -/
lemma rankOneFamilyAtlas_divisor :
    familyAtlasRelativeFiberEquiv h L hL hV (rankOneFamilyAtlas h L hL hV hN) =
      rankOneFamilyDivisor h L hL hV hN :=
  (familyAtlasRelativeFiberEquiv h L hL hV).apply_symm_apply _

/-- Rank-one test families have only this original map to the universal divisor atlas. -/
theorem rankOneFamilyAtlas_unique (a : TestMorphism L hL hV (g := g)) :
    a = rankOneFamilyAtlas h L hL hV hN := by
  apply (familyAtlasRelativeFiberEquiv h L hL hV).injective
  rw [rankOneFamilyAtlas_divisor]
  exact rankOneFamilyDivisor_unique h L hL hV hN _

/-- The canonical divisor is a full geometric comap of the constructed universal ideal. -/
theorem rankOneFamilyDivisor_universalIdeal :
    (rankOneFamilyDivisor h L hL hV hN).val.val.val =
      (ProperUniversalDirectImage.universalIdeal f L hL hV).comap
        (atlasFamilyMap h L hL hV (rankOneFamilyAtlas h L hL hV hN)) := by
  rw [← rankOneFamilyAtlas_divisor h L hL hV hN]
  exact familyAtlasRelativeFiberEquiv_ideal h L hL hV _

variable {Q U : Scheme.{0}} {p' : Q ⟶ X} {q' : Q ⟶ U} {g' : U ⟶ S}
  (h' : IsPullback p' q' f g')
  (hN' : LocallyFreeRankOne ((pushforward q').obj ((pullback p').obj L)))
  (k : U ⟶ T) (r : Q ⟶ P)
  (hp : r ≫ p = p') (hq : r ≫ q = q' ≫ k) (hg : k ≫ g = g')

include hp hq hg in
/-- Normalized divisors commute with actual total-space pullback as full ideal sheaves. -/
theorem rankOneFamilyDivisor_natural_ideal :
    (rankOneFamilyDivisor h' L hL hV hN').val.val.val =
      (rankOneFamilyDivisor h L hL hV hN).val.val.val.comap r := by
  have hn := familyAtlasRelativeFiberEquiv_natural_ideal h L hL hV h' k r hp hq hg
    (rankOneFamilyAtlas h L hL hV hN)
  rw [rankOneFamilyAtlas_divisor] at hn
  have he := rankOneFamilyDivisor_unique h' L hL hV hN'
    (familyAtlasRelativeFiberEquiv h' L hL hV
      (familyAtlasPrecomp L hL hV k hg (rankOneFamilyAtlas h L hL hV hN)))
  exact (congrArg (fun D : RelativeFiber q' ((pullback p').obj L) (hL.pullback p') ↦
    D.val.val.val) he).symm.trans hn

end FLT.Mazur.CartierAbel
