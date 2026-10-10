/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyOrbitPullback
public import FLT.Mazur.ProperFamilyNaturalRepresentation

/-!
# Natural equivalences for original geometric section orbits

The orbit presheaf uses direct pullback of original twisting lines and sections.
Its equivalences with the atlas and the full divisor fiber commute with every
actual original test-family morphism, including iterated morphisms and identities.
The small atlas and divisor types are lifted to the universe of original section orbits.
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

/-- The original section-orbit presheaf uses direct geometric pullback on representatives. -/
def familyOrbitFunctor : (Family f)ᵒᵖ ⥤ Type _ where
  obj A := Quotient (familyBaseLineSetoid A.unop.square L hL hV)
  map u := TypeCat.ofHom (familyOrbitMap L hL hV u.unop)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro s
    exact familyOrbitMap_id L hL hV s
  map_comp u v := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (familyOrbitMap_comp L hL hV v.unop u.unop s).symm

/-- Actual original twisting-line orbits naturally identify with actual atlas morphisms. -/
def familyOrbitAtlasNatIso : familyOrbitFunctor L hL hV ≅
    familyAtlasFunctor L hL hV ⋙ uliftFunctor.{1} :=
  NatIso.ofComponents (fun A ↦
    ((familyBaseLineAtlasEquiv A.unop.square L hL hV).trans Equiv.ulift.symm).toIso)
    (by
      intro A B u
      apply ConcreteCategory.hom_ext
      intro s
      apply ULift.ext
      exact familyOrbitMap_toAtlas L hL hV u.unop s)

/-- Direct geometric original-section orbits naturally classify the entire relative Abel fiber. -/
def familyOrbitFiberNatIso : familyOrbitFunctor L hL hV ≅
    familyFiberFunctor L hL hV ⋙ uliftFunctor.{1} :=
  familyOrbitAtlasNatIso L hL hV ≪≫ Functor.isoWhiskerRight (familyAtlasFiberNatIso L hL hV) _

/-- The natural equivalence preserves every original section's full zero divisor. -/
lemma familyOrbitFiberNatIso_hom_mk (A : Family f)
    (s : RelativeSection A.snd ((pullback A.fst).obj L) (hL.pullback A.fst)) :
    ((familyOrbitFiberNatIso L hL hV).hom.app (op A) (Quotient.mk _ s)).down =
      relativeSectionToFiber A.snd ((pullback A.fst).obj L) (hL.pullback A.fst) s :=
  familyAtlasRelativeFiberEquiv_toFamilyAtlas A.square L hL hV s

/-- Naturality on original representatives uses their directly pulled tensor sections. -/
lemma familyOrbitFiberNatIso_natural_section {A B : Family f} (u : A ⟶ B)
    (s : RelativeSection B.snd ((pullback B.fst).obj L) (hL.pullback B.fst)) :
    ((familyOrbitFiberNatIso L hL hV).hom.app (op A)
        (Quotient.mk _ (familySectionMap L hL hV u s))).down =
      (familyFiberFunctor L hL hV).map u.op
        ((familyOrbitFiberNatIso L hL hV).hom.app (op B) (Quotient.mk _ s)).down := by
  rw [familyOrbitFiberNatIso_hom_mk, familyOrbitFiberNatIso_hom_mk]
  exact familySectionPullback_toFiber B.square L hL hV A.square
    u.base u.total u.fst u.snd u.over s

end FLT.Mazur.CartierAbel
