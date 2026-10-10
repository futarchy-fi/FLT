/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassFourTorsionEtale
public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Auxiliary markings as open and closed four-torsion sections

Each original marking factors through the actual torsion equalizer and its
base change to the level scheme. These sections are open and closed even over
nonreduced tests; no identification of point sets with schemes is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

/-- The original marking factored through the full torsion equation. -/
def auxiliaryTorsionMarking (a : Labels 4) : levelFour ⟶ fourTorsion :=
  GroupTorsionScheme.lift universalGroup 4 (auxiliaryMarking 4 a) (auxiliaryMarking_pow 4 a)

/-- Factoring the marking does not change its value in the original cubic. -/
@[reassoc (attr := simp)] theorem auxiliaryTorsionMarking_inclusion (a : Labels 4) :
    auxiliaryTorsionMarking a ≫ GroupTorsionScheme.inclusion universalGroup 4 =
      auxiliaryMarking 4 a := GroupTorsionScheme.lift_inclusion _ _ _ _

/-- The full torsion scheme after base change to the auxiliary level scheme. -/
def auxiliaryFourTorsion : Scheme := pullback fourTorsion.hom levelFour.hom

/-- Its original structure morphism over the auxiliary level scheme. -/
def auxiliaryFourTorsionMap : auxiliaryFourTorsion ⟶ levelFour.left :=
  pullback.snd fourTorsion.hom levelFour.hom

/-- The base-changed torsion scheme remains finite. -/
instance auxiliaryFourTorsionMap_finite : IsFinite auxiliaryFourTorsionMap :=
  inferInstanceAs (IsFinite (pullback.snd fourTorsion.hom levelFour.hom))

/-- The base-changed torsion scheme remains etale. -/
instance auxiliaryFourTorsionMap_etale : Etale auxiliaryFourTorsionMap :=
  inferInstanceAs (Etale (pullback.snd fourTorsion.hom levelFour.hom))

/-- Each original auxiliary marking is a section of the base-changed torsion scheme. -/
def auxiliaryTorsionSection (a : Labels 4) : levelFour.left ⟶ auxiliaryFourTorsion :=
  pullback.lift (auxiliaryTorsionMarking a).left (𝟙 _) (by
    simpa only [Category.id_comp] using (auxiliaryTorsionMarking a).w)

/-- The factored marking is a genuine section over the level scheme. -/
@[reassoc (attr := simp)] theorem auxiliaryTorsionSection_map (a : Labels 4) :
    auxiliaryTorsionSection a ≫ auxiliaryFourTorsionMap = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Projection recovers the original torsion-valued marking. -/
@[reassoc (attr := simp)] theorem auxiliaryTorsionSection_fst (a : Labels 4) :
    auxiliaryTorsionSection a ≫ pullback.fst fourTorsion.hom levelFour.hom =
      (auxiliaryTorsionMarking a).left := pullback.lift_fst _ _ _

/-- Each label cuts out an open component of the full torsion scheme. -/
instance auxiliaryTorsionSection_open (a : Labels 4) :
    IsOpenImmersion (auxiliaryTorsionSection a) :=
  UnramifiedSectionImmersion.isOpenImmersion auxiliaryFourTorsionMap _
    (auxiliaryTorsionSection_map a)

/-- Each label also cuts out a closed component. -/
instance auxiliaryTorsionSection_closed (a : Labels 4) :
    IsClosedImmersion (auxiliaryTorsionSection a) :=
  UnramifiedSectionImmersion.isClosedImmersion auxiliaryFourTorsionMap _
    (auxiliaryTorsionSection_map a)

end FLT.Mazur.UniversalWeierstrass
