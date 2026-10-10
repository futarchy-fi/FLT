/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyDivisorNaturality

/-!
# Pullback of the original relative Abel fibers

The represented fiber gives membership of the pulled full ideal in the
original target fiber. The resulting map retains the actual total-space map.
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

/-- Pull an original divisor along a map of original cartesian test families. -/
def familyFiberPullback
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    RelativeFiber q' ((pullback p').obj L) (hL.pullback p') :=
  familyAtlasRelativeFiberEquiv h' L hL hV
    (familyAtlasPrecomp L hL hV k hg ((familyAtlasRelativeFiberEquiv h L hL hV).symm D))

include hp hq in
/-- Fiber pullback is exactly comap of the full original ideal, including multiplicities. -/
lemma familyFiberPullback_ideal
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    (familyFiberPullback h L hL hV h' k hg D).val.val.val = D.val.val.val.comap r := by
  unfold familyFiberPullback
  rw [familyAtlasRelativeFiberEquiv_natural_ideal h L hL hV h' k r hp hq hg,
    Equiv.apply_symm_apply]

/-- The original representing equivalence intertwines actual atlas and divisor pullbacks. -/
lemma familyAtlasRelativeFiberEquiv_natural (a : TestMorphism L hL hV (g := g)) :
    familyAtlasRelativeFiberEquiv h' L hL hV (familyAtlasPrecomp L hL hV k hg a) =
      familyFiberPullback h L hL hV h' k hg (familyAtlasRelativeFiberEquiv h L hL hV a) := by
  unfold familyFiberPullback
  rw [Equiv.symm_apply_apply]

/-- The inverse representing map also commutes with original-family pullback. -/
lemma familyAtlasRelativeFiberEquiv_symm_natural
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    (familyAtlasRelativeFiberEquiv h' L hL hV).symm
        (familyFiberPullback h L hL hV h' k hg D) =
      familyAtlasPrecomp L hL hV k hg ((familyAtlasRelativeFiberEquiv h L hL hV).symm D) :=
  (familyAtlasRelativeFiberEquiv h' L hL hV).symm_apply_apply _

end FLT.Mazur.CartierAbel
