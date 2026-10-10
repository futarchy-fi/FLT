/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLinePrincipalRestriction
public import FLT.Mazur.NormalizedSectionLineRechart

/-!
# Recharting a section line on its actual principal open

Localizing at any generator coordinate makes that coordinate invertible.
The resulting new chart is constructed on the same localized submodule,
and the explicit principal restriction comparison preserves its inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R : Type u} [CommRing R] {ι : Type u}

/-- The selected generator coordinate is a unit in its own principal localization. -/
def principalCoordinateUnit (i j : ι) (L : Chart R ι i) :
    (Localization.Away (generator R ι i L j))ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (generator R ι i L j))
    (generator R ι i L j)).unit

/-- The localized generator coordinate is the constructed unit. -/
lemma principalCoordinateUnit_spec (i j : ι) (L : Chart R ι i) :
    generator (Localization.Away (generator R ι i L j)) ι i
        (baseChange (algebraMap R (Localization.Away (generator R ι i L j))) i L) j =
      (principalCoordinateUnit i j L : Localization.Away (generator R ι i L j)) := by
  rw [generator_baseChange]
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (generator R ι i L j)) (generator R ι i L j)).unit_spec.symm

/-- The new coordinate chart on the genuine principal localization of the test ring. -/
def principalRechart (i j : ι) (L : Chart R ι i) :
    Chart (Localization.Away (generator R ι i L j)) ι j :=
  rechart i j (baseChange (algebraMap R (Localization.Away (generator R ι i L j))) i L)
    (principalCoordinateUnit i j L) (principalCoordinateUnit_spec i j L)

/-- The recharted sheaf is the actual principal restriction of the original sheaf line. -/
def sheafPrincipalRechart (i j : ι) (L : Chart R ι i) :
    (principalRestriction (generator R ι i L j)).obj (sheaf i L) ≅
      sheaf j (principalRechart i j L) :=
  sheafPrincipalRestriction (generator R ι i L j) i L ≪≫
    sheafChartChange i j _ _ rfl

attribute [local irreducible] sheafPrincipalRestriction sheafChartChange
attribute [local irreducible] principalRestriction vectorPrincipalRestriction

/-- Principal recharting preserves the actual ambient inclusion. -/
lemma sheafPrincipalRechart_inclusion [Finite ι] (i j : ι) (L : Chart R ι i) :
    (sheafPrincipalRechart i j L).hom ≫ sheafInclusion j (principalRechart i j L) =
      (principalRestriction (generator R ι i L j)).map (sheafInclusion i L) ≫
        (vectorPrincipalRestriction (ι := ι) (generator R ι i L j)).hom := by
  simp only [sheafPrincipalRechart, Iso.trans_hom, Category.assoc,
    sheafChartChange_inclusion, sheafPrincipalRestriction_inclusion]

end FLT.Mazur.NormalizedSectionLine
