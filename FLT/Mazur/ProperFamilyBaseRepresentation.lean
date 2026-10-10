/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyCanonicalTests
public import FLT.Mazur.ProperFamilyOrbitFunctor

/-!
# Representability of the relative Cartier Abel fiber on all test bases

Restriction to canonical cartesian families gives presheaves on schemes over
the fixed base. The actual original dual projective atlas represents the fiber,
with the same full-ideal pullback map as the relative Picard construction.
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

/-- The relative Cartier Abel fiber presheaf on all schemes over the original base. -/
def familyBaseFiberFunctor : (Over S)ᵒᵖ ⥤ Type _ :=
  (canonicalFamilyFunctor f).op ⋙ familyFiberFunctor L hL hV

/-- The actual atlas-map presheaf on all schemes over the original base. -/
def familyBaseAtlasFunctor : (Over S)ᵒᵖ ⥤ Type _ :=
  (canonicalFamilyFunctor f).op ⋙ familyAtlasFunctor L hL hV

/-- The geometric original-section orbit presheaf on all schemes over the original base. -/
def familyBaseOrbitFunctor : (Over S)ᵒᵖ ⥤ Type _ :=
  (canonicalFamilyFunctor f).op ⋙ familyOrbitFunctor L hL hV

/-- Atlas maps with their original base equation are exactly morphisms in the over category. -/
def familyAtlasOverEquiv (T : Over S) :
    TestMorphism L hL hV (g := T.hom) ≃ (T ⟶ Over.mk π) where
  toFun a := Over.homMk a.val a.property
  invFun a := ⟨a.left, a.w⟩
  left_inv a := Subtype.ext rfl
  right_inv a := by ext; rfl

/-- The actual atlas-map presheaf is the usual represented presheaf. -/
def familyBaseAtlasYonedaIso : familyBaseAtlasFunctor L hL hV ≅ yoneda.obj (Over.mk π) :=
  NatIso.ofComponents (fun T ↦ (familyAtlasOverEquiv L hL hV T.unop).toIso)
    (by
      intro T U u
      apply ConcreteCategory.hom_ext
      intro a
      rfl)

/-- The original dual projective atlas represents the relative Abel fiber on every test base. -/
def familyBaseFiberRepresentation : yoneda.obj (Over.mk π) ≅ familyBaseFiberFunctor L hL hV :=
  (familyBaseAtlasYonedaIso L hL hV).symm ≪≫
    Functor.isoWhiskerLeft (canonicalFamilyFunctor f).op (familyAtlasFiberNatIso L hL hV)

/-- Every base morphism acts by full ideal comap along the original Picard total-space map. -/
lemma familyBaseFiberFunctor_map_ideal {T U : Over S} (u : T ⟶ U)
    (D : (familyBaseFiberFunctor L hL hV).obj (op U)) :
    ((familyBaseFiberFunctor L hL hV).map u.op D).val.val.val =
      D.val.val.val.comap (SchemePicard.relativeTotalMap f u) :=
  familyFiberFunctor_map_ideal L hL hV ((canonicalFamilyFunctor f).map u) D

end FLT.Mazur.CartierAbel
