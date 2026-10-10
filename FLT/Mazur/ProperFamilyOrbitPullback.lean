/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyOriginalPullback

/-!
# Geometric pullback on original twisting-line orbits

Pullback acts on representatives by pulling their actual original twists and
sections. The orbit laws follow from the proved full geometric representation.
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

variable {A B C : Family f}

/-- The original section pullback on a specified morphism of test families. -/
def familySectionMap (u : A ⟶ B)
    (s : RelativeSection B.snd ((pullback B.fst).obj L) (hL.pullback B.fst)) :
    RelativeSection A.snd ((pullback A.fst).obj L) (hL.pullback A.fst) :=
  familySectionPullback B.square L hL hV A.square u.base u.total u.fst u.snd u.over s

/-- The actual representing morphism of the directly pulled original section. -/
lemma familySectionMap_toAtlas (u : A ⟶ B)
    (s : RelativeSection B.snd ((pullback B.fst).obj L) (hL.pullback B.fst)) :
    (familySectionMap L hL hV u s).toFamilyAtlas A.square L hL hV =
      familyAtlasPrecomp L hL hV u.base u.over (s.toFamilyAtlas B.square L hL hV) :=
  familySectionPullback_toAtlas B.square L hL hV A.square
    u.base u.total u.fst u.snd u.over s

/-- Direct original section pullback respects isomorphisms of original twisting lines. -/
lemma familySectionMap_rel (u : A ⟶ B)
    (s t : RelativeSection B.snd ((pullback B.fst).obj L) (hL.pullback B.fst))
    (hst : (familyBaseLineSetoid B.square L hL hV).r s t) :
    (familyBaseLineSetoid A.square L hL hV).r
      (familySectionMap L hL hV u s) (familySectionMap L hL hV u t) := by
  apply (toFamilyAtlas_eq_iff A.square L hL hV _ _).mp
  rw [familySectionMap_toAtlas, familySectionMap_toAtlas,
    (toFamilyAtlas_eq_iff B.square L hL hV s t).mpr hst]

/-- Pull original twisting-line orbits by direct geometric pullback of representatives. -/
def familyOrbitMap (u : A ⟶ B) : Quotient (familyBaseLineSetoid B.square L hL hV) →
    Quotient (familyBaseLineSetoid A.square L hL hV) :=
  Quotient.map (familySectionMap L hL hV u) (familySectionMap_rel L hL hV u)

/-- The original orbit equivalence commutes with direct geometric section pullback. -/
lemma familyOrbitMap_toAtlas (u : A ⟶ B)
    (s : Quotient (familyBaseLineSetoid B.square L hL hV)) :
    familyBaseLineAtlasEquiv A.square L hL hV (familyOrbitMap L hL hV u s) =
      familyAtlasPrecomp L hL hV u.base u.over (familyBaseLineAtlasEquiv B.square L hL hV s) := by
  induction s using Quotient.inductionOn with | h s =>
    exact familySectionMap_toAtlas L hL hV u s

/-- The identity geometric pullback preserves the full original twisting-line orbit. -/
lemma familyOrbitMap_id (s : Quotient (familyBaseLineSetoid A.square L hL hV)) :
    familyOrbitMap L hL hV (𝟙 A) s = s := by
  apply (familyBaseLineAtlasEquiv A.square L hL hV).injective
  rw [familyOrbitMap_toAtlas]
  exact familyAtlasPrecomp_id L hL hV _

/-- Iterated geometric pullback equals pullback along the actual composite family map. -/
lemma familyOrbitMap_comp (u : A ⟶ B) (v : B ⟶ C)
    (s : Quotient (familyBaseLineSetoid C.square L hL hV)) :
    familyOrbitMap L hL hV u (familyOrbitMap L hL hV v s) =
      familyOrbitMap L hL hV (u ≫ v) s := by
  apply (familyBaseLineAtlasEquiv A.square L hL hV).injective
  rw [familyOrbitMap_toAtlas, familyOrbitMap_toAtlas, familyOrbitMap_toAtlas]
  exact familyAtlasPrecomp_comp L hL hV v.base u.base v.over u.over _

end FLT.Mazur.CartierAbel
