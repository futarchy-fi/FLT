/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyLineClassification
public import FLT.Mazur.ProperFamilySplitDirectImageSections
public import FLT.Mazur.OriginalTwistOrbitRelation

/-!
# Original relative section orbits represented over arbitrary test bases

The actual atlas represents relative sections modulo isomorphisms of their
original twisting lines. All maps use the independently given family square
and its direct-image mate; the test base is unrestricted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open ProperFamilyAtlas FCurve LineSectionBaseChange DualAtlasLineQuotient
open LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
attribute [local irreducible] ProperFamilyAtlas.morphism
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

/-- The original relative section supplies its original dual-line inclusion. -/
def RelativeSection.familyLine (s : R) : Line N :=
  (s.toFamilySplitDirectImage h L hL hV).toLine q ((pullback p).obj L)

/-- The actual morphism to the original atlas, with its original base map. -/
def RelativeSection.toFamilyAtlas (s : R) : TestMorphism L hL hV (g := g) :=
  ⟨morphism h L hL hV (s.familyLine h L hL hV),
    morphism_projection h L hL hV (s.familyLine h L hL hV)⟩

/-- The original retained twisting-line relation on relative sections. -/
def familyBaseLineSetoid : Setoid R :=
  (lineSetoid N).comap (RelativeSection.familyLine h L hL hV)

/-- Equality in the actual original atlas detects exactly the original twisting-line orbit. -/
lemma toFamilyAtlas_eq_iff (s t : R) :
    s.toFamilyAtlas h L hL hV = t.toFamilyAtlas h L hL hV ↔
      (familyBaseLineSetoid h L hL hV).r s t := by
  rw [Subtype.ext_iff]
  exact morphism_eq_iff h L hL hV _ _

/-- Recover a relative section on the original family from an actual atlas morphism. -/
def familySectionOfAtlas (a : TestMorphism L hL hV (g := g)) : R :=
  (splitDirectImageOfLine q ((pullback p).obj L)
    (lineOfMorphism h L hL hV a)).toFamilyRelative h L hL hV

/-- Reconstruction recovers the entire original atlas morphism. -/
lemma toFamilyAtlas_familySectionOfAtlas (a : TestMorphism L hL hV (g := g)) :
    (familySectionOfAtlas h L hL hV a).toFamilyAtlas h L hL hV = a := by
  apply Subtype.ext
  dsimp only [RelativeSection.toFamilyAtlas, RelativeSection.familyLine, familySectionOfAtlas]
  rw [toFamilySplitDirectImage_toFamilyRelative]
  exact ((morphism_eq_iff h L hL hV _ _).mpr
    (lineOfSplitDirectImageOfLine q ((pullback p).obj L) _)).trans
      (morphism_lineOfMorphism h L hL hV a)

/-- The actual atlas morphism descends through original twisting-line isomorphisms. -/
def familyBaseLineQuotientToAtlas :
    Quotient (familyBaseLineSetoid h L hL hV) → TestMorphism L hL hV (g := g) :=
  Quotient.lift (RelativeSection.toFamilyAtlas h L hL hV)
    (fun s t hs ↦ (toFamilyAtlas_eq_iff h L hL hV s t).mpr hs)

/-- The original scheme atlas represents the original twisting-line orbits on every test base. -/
def familyBaseLineAtlasEquiv :
    Quotient (familyBaseLineSetoid h L hL hV) ≃ TestMorphism L hL hV (g := g) where
  toFun := familyBaseLineQuotientToAtlas h L hL hV
  invFun a := Quotient.mk _ (familySectionOfAtlas h L hL hV a)
  left_inv a := by
    induction a using Quotient.inductionOn with | h s =>
      exact Quotient.sound ((toFamilyAtlas_eq_iff h L hL hV _ _).mp
        (toFamilyAtlas_familySectionOfAtlas h L hL hV (s.toFamilyAtlas h L hL hV)))
  right_inv := toFamilyAtlas_familySectionOfAtlas h L hL hV

/-- The orbit equivalence retains the actual atlas map of each original relative section. -/
lemma familyBaseLineAtlasEquiv_mk (s : R) :
    familyBaseLineAtlasEquiv h L hL hV (Quotient.mk _ s) =
      s.toFamilyAtlas h L hL hV := rfl

end FLT.Mazur.CartierAbel
