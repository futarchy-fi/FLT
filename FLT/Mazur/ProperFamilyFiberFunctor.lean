/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyFiberPullback
public import FLT.Mazur.ProperFamilyTestCategory

/-!
# Contravariant functors of original atlas maps and Cartier Abel fibers

Composition retains the actual maps of test bases. Full ideal comap identifies
the divisor functor with geometric pullback on each original total space.
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

omit [GeometricallyIntegral f] in
/-- Identity precomposition retains the entire original atlas morphism. -/
lemma familyAtlasPrecomp_id (a : TestMorphism L hL hV (g := g)) :
    familyAtlasPrecomp L hL hV (𝟙 T) (Category.id_comp g) a = a :=
  Subtype.ext (Category.id_comp a.val)

omit [GeometricallyIntegral f] in
/-- Iterated precomposition uses the actual composite map of original bases. -/
lemma familyAtlasPrecomp_comp {U V : Scheme.{0}} {g' : U ⟶ S} {g'' : V ⟶ S}
    (k : U ⟶ T) (l : V ⟶ U) (hk : k ≫ g = g') (hl : l ≫ g' = g'')
    (a : TestMorphism L hL hV (g := g)) :
    familyAtlasPrecomp L hL hV l hl (familyAtlasPrecomp L hL hV k hk a) =
      familyAtlasPrecomp L hL hV (l ≫ k) (by rw [Category.assoc, hk, hl]) a :=
  Subtype.ext (Category.assoc l k a.val).symm

/-- Identity pullback on the actual original relative fiber. -/
lemma familyFiberPullback_id
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    familyFiberPullback h L hL hV h (𝟙 T) (Category.id_comp g) D = D := by
  unfold familyFiberPullback
  rw [familyAtlasPrecomp_id, Equiv.apply_symm_apply]

/-- Iterated pullback on arbitrary original test families is strictly compositional. -/
lemma familyFiberPullback_comp {Q U V W : Scheme.{0}}
    {p' : Q ⟶ X} {q' : Q ⟶ U} {g' : U ⟶ S} (h' : IsPullback p' q' f g')
    {p'' : W ⟶ X} {q'' : W ⟶ V} {g'' : V ⟶ S} (h'' : IsPullback p'' q'' f g'')
    (k : U ⟶ T) (l : V ⟶ U) (hk : k ≫ g = g') (hl : l ≫ g' = g'')
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    familyFiberPullback h' L hL hV h'' l hl (familyFiberPullback h L hL hV h' k hk D) =
      familyFiberPullback h L hL hV h'' (l ≫ k) (by rw [Category.assoc, hk, hl]) D := by
  unfold familyFiberPullback
  rw [Equiv.symm_apply_apply, familyAtlasPrecomp_comp]

open ProperFamilyTests Opposite

/-- The original atlas's points form a presheaf on cartesian test families. -/
def familyAtlasFunctor : (Family f)ᵒᵖ ⥤ Type _ where
  obj A := TestMorphism L hL hV (g := A.unop.toBase)
  map u := TypeCat.ofHom (familyAtlasPrecomp L hL hV u.unop.base u.unop.over)
  map_id A := by apply ConcreteCategory.hom_ext; intro a; exact familyAtlasPrecomp_id L hL hV a
  map_comp u v := by apply ConcreteCategory.hom_ext; intro a; exact (familyAtlasPrecomp_comp L hL hV
    u.unop.base v.unop.base u.unop.over v.unop.over a).symm

/-- The full relative Cartier Abel fibers form a presheaf on original test families. -/
def familyFiberFunctor : (Family f)ᵒᵖ ⥤ Type _ where
  obj A := RelativeFiber A.unop.snd ((pullback A.unop.fst).obj L) (hL.pullback A.unop.fst)
  map {A B} u := TypeCat.ofHom (familyFiberPullback A.unop.square L hL hV B.unop.square
    u.unop.base u.unop.over)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro D
    exact familyFiberPullback_id A.unop.square L hL hV D
  map_comp {A B C} u v := by
    apply ConcreteCategory.hom_ext
    intro D
    exact (familyFiberPullback_comp A.unop.square L hL hV B.unop.square C.unop.square
      u.unop.base v.unop.base u.unop.over v.unop.over D).symm

/-- Every presheaf map pulls the full ideal along the specified original total-space map. -/
lemma familyFiberFunctor_map_ideal {A B : Family f} (u : A ⟶ B)
    (D : (familyFiberFunctor L hL hV).obj (op B)) :
    ((familyFiberFunctor L hL hV).map u.op D).val.val.val = D.val.val.val.comap u.total :=
  familyFiberPullback_ideal B.square L hL hV A.square u.base u.total u.fst u.snd u.over D

end FLT.Mazur.CartierAbel
