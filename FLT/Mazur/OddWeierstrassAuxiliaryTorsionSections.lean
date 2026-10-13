/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassThreeTorsionEtale
public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Auxiliary markings as open and closed three-torsion sections

Each original marking factors through the actual torsion equalizer and its
base change to the level scheme. These sections are open and closed even over
nonreduced tests; no identification of point sets with schemes is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing)
open UniversalWeierstrass (Labels labels_pow)

/-- The original marking factored through the full torsion equation. -/
def auxiliaryTorsionMarking (a : Labels 3) : levelThree ⟶ threeTorsion :=
  GroupTorsionScheme.lift universalGroup 3 (levelThreeMarking a) (levelThreeMarking_pow a)

/-- Factoring the marking does not change its value in the original cubic. -/
@[reassoc (attr := simp)] theorem auxiliaryTorsionMarking_inclusion (a : Labels 3) :
    auxiliaryTorsionMarking a ≫ GroupTorsionScheme.inclusion universalGroup 3 =
      levelThreeMarking a := GroupTorsionScheme.lift_inclusion _ _ _ _

/-- The full torsion scheme after base change to the auxiliary level scheme. -/
def auxiliaryThreeTorsion : Scheme := pullback threeTorsion.hom levelThree.hom

/-- Its original structure morphism over the auxiliary level scheme. -/
def auxiliaryThreeTorsionMap : auxiliaryThreeTorsion ⟶ levelThree.left :=
  pullback.snd threeTorsion.hom levelThree.hom

/-- The base-changed torsion scheme remains finite. -/
instance auxiliaryThreeTorsionMap_finite : IsFinite auxiliaryThreeTorsionMap :=
  inferInstanceAs (IsFinite (pullback.snd threeTorsion.hom levelThree.hom))

/-- The base-changed torsion scheme remains etale. -/
instance auxiliaryThreeTorsionMap_etale : Etale auxiliaryThreeTorsionMap :=
  inferInstanceAs (Etale (pullback.snd threeTorsion.hom levelThree.hom))

/-- Each original auxiliary marking is a section of the base-changed torsion scheme. -/
def auxiliaryTorsionSection (a : Labels 3) : levelThree.left ⟶ auxiliaryThreeTorsion :=
  pullback.lift (auxiliaryTorsionMarking a).left (𝟙 _) (by
    simpa only [Category.id_comp] using (auxiliaryTorsionMarking a).w)

/-- The factored marking is a genuine section over the level scheme. -/
@[reassoc (attr := simp)] theorem auxiliaryTorsionSection_map (a : Labels 3) :
    auxiliaryTorsionSection a ≫ auxiliaryThreeTorsionMap = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Projection recovers the original torsion-valued marking. -/
@[reassoc (attr := simp)] theorem auxiliaryTorsionSection_fst (a : Labels 3) :
    auxiliaryTorsionSection a ≫ pullback.fst threeTorsion.hom levelThree.hom =
      (auxiliaryTorsionMarking a).left := pullback.lift_fst _ _ _

/-- Each label cuts out an open component of the full torsion scheme. -/
instance auxiliaryTorsionSection_open (a : Labels 3) :
    IsOpenImmersion (auxiliaryTorsionSection a) :=
  UnramifiedSectionImmersion.isOpenImmersion auxiliaryThreeTorsionMap _
    (auxiliaryTorsionSection_map a)

/-- Each label also cuts out a closed component. -/
instance auxiliaryTorsionSection_closed (a : Labels 3) :
    IsClosedImmersion (auxiliaryTorsionSection a) :=
  UnramifiedSectionImmersion.isClosedImmersion auxiliaryThreeTorsionMap _
    (auxiliaryTorsionSection_map a)

end FLT.Mazur.OddWeierstrassParameter
