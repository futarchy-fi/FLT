/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyFiberFunctor

/-!
# Natural representation of the original relative Cartier Abel fiber

The pointwise original-family equivalences assemble into a natural isomorphism
of presheaves, with the inverse retaining the original atlas morphism.
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

open ProperFamilyTests Opposite

/-- The original dual projective atlas naturally represents the full relative Abel fiber. -/
def familyAtlasFiberNatIso : familyAtlasFunctor L hL hV ≅ familyFiberFunctor L hL hV :=
  NatIso.ofComponents
    (fun A ↦ (familyAtlasRelativeFiberEquiv A.unop.square L hL hV).toIso)
    (by
      intro A B u
      apply ConcreteCategory.hom_ext
      intro a
      exact familyAtlasRelativeFiberEquiv_natural A.unop.square L hL hV
        B.unop.square u.unop.base u.unop.over a)

/-- The natural representation is the independently proved original-family equivalence. -/
lemma familyAtlasFiberNatIso_hom (A : Family f)
    (a : TestMorphism L hL hV (g := A.toBase)) :
    (familyAtlasFiberNatIso L hL hV).hom.app (op A) a =
      familyAtlasRelativeFiberEquiv A.square L hL hV a := rfl

/-- The inverse natural representation retains each original section's actual atlas map. -/
lemma familyAtlasFiberNatIso_inv_section (A : Family f)
    (s : RelativeSection A.snd ((pullback A.fst).obj L) (hL.pullback A.fst)) :
    (familyAtlasFiberNatIso L hL hV).inv.app (op A)
        (relativeSectionToFiber A.snd ((pullback A.fst).obj L) (hL.pullback A.fst) s) =
      s.toFamilyAtlas A.square L hL hV :=
  familyAtlasRelativeFiberEquiv_symm_section A.square L hL hV s

/-- Natural representation retains geometric pullback of the full original ideal. -/
lemma familyAtlasFiberNatIso_natural_ideal {A B : Family f} (u : A ⟶ B)
    (a : TestMorphism L hL hV (g := B.toBase)) :
    ((familyAtlasFiberNatIso L hL hV).hom.app (op A)
      ((familyAtlasFunctor L hL hV).map u.op a)).val.val.val =
        ((familyAtlasFiberNatIso L hL hV).hom.app (op B) a).val.val.val.comap u.total :=
  familyAtlasRelativeFiberEquiv_natural_ideal B.square L hL hV A.square
    u.base u.total u.fst u.snd u.over a

end FLT.Mazur.CartierAbel
