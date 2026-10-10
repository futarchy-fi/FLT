/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineTransport
public import FLT.Mazur.ModuleLineBundlePullback

/-!
# Rank one of actual affine section lines

The coordinate projection trivializes the actual line sheaf. This gives
local rank one on arbitrary test schemes, without choosing a test trivialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections NormalizedSectionLine FCurve
variable (S : Scheme.{u}) [IsAffine S]
variable {ι : Type u}

/-- The affine coordinate projection trivializes the genuine section-line sheaf. -/
def sectionLineTrivialization (i : ι) (L : Chart Γ(S, ⊤) ι i) :
    sectionLineSheaf S i L ≅ structureModule S :=
  (affineTilde S).mapIso (trivialization Γ(S, ⊤) ι i L).toModuleIso ≪≫
    (pullback S.isoSpec.hom).mapIso tildeSelf ≪≫ modulePullbackUnitIso S.isoSpec.hom

/-- The actual section line is locally free of rank one. -/
lemma sectionLineSheaf_rankOne (i : ι) (L : Chart Γ(S, ⊤) ι i) :
    LocallyFreeRankOne (sectionLineSheaf S i L) :=
  structureModule_locallyFreeRankOne.of_iso (sectionLineTrivialization S i L).symm

/-- The original coordinate trivialization pulls back to every test scheme. -/
def testSectionLineTrivialization {T : Scheme.{u}} (f : T ⟶ S)
    (i : ι) (L : Chart Γ(S, ⊤) ι i) :
    (pullback f).obj (sectionLineSheaf S i L) ≅ structureModule T :=
  (pullback f).mapIso (sectionLineTrivialization S i L) ≪≫ modulePullbackUnitIso f

/-- Every test pullback of the actual line retains local rank one. -/
lemma testSectionLineSheaf_rankOne {T : Scheme.{u}} (f : T ⟶ S)
    (i : ι) (L : Chart Γ(S, ⊤) ι i) :
    LocallyFreeRankOne ((pullback f).obj (sectionLineSheaf S i L)) :=
  (sectionLineSheaf_rankOne S i L).pullback f

end FLT.Mazur.AffineFreeSheafCoordinates
