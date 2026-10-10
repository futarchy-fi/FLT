/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesProjOverlap
public import FLT.Mazur.WeierstrassSuccessiveReesGluing

/-!
# The successive modification maps to its original Rees Proj

The proved overlap square glues the two standard-open maps. Transport
through the fraction atlas gives a map from the actual equation modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R) (hπ : π ≠ 0)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

/-- The two standard fraction inclusions glue to the same Rees scheme. -/
def fractionAtlasToProj : fractionAtlas W s π b3 b4 b6 hπ ⟶ BlowupRees.proj I :=
  pushout.desc (horizontalProjInclusion W s π b3 b4 b6)
    (scaleProjInclusion W s π b3 b4 b6)
    (horizontalOverlap_toProj W s π b3 b4 b6 hπ).symm

/-- The glued comparison retains the horizontal standard-open map. -/
@[reassoc] theorem horizontalChart_toProj :
    horizontalChart W s π b3 b4 b6 hπ ≫ fractionAtlasToProj W s π b3 b4 b6 hπ =
      horizontalProjInclusion W s π b3 b4 b6 := pushout.inl_desc _ _ _

/-- The glued comparison retains the scale standard-open map. -/
@[reassoc] theorem scaleChart_toProj :
    scaleChart W s π b3 b4 b6 hπ ≫ fractionAtlasToProj W s π b3 b4 b6 hπ =
      scaleProjInclusion W s π b3 b4 b6 := pushout.inr_desc _ _ _

/-- The actual two-equation modification maps to the Rees Proj of its preceding center. -/
def modificationToProj :
    WeierstrassSuccessiveX.modification W s π b3 b4 b6 ⟶ BlowupRees.proj I :=
  (fractionAtlasIso W s π b3 b4 b6 hπ).inv ≫ fractionAtlasToProj W s π b3 b4 b6 hπ

end FLT.Mazur.WeierstrassSuccessiveRees
