/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassFourTorsionFinite
public import FLT.Mazur.UniversalWeierstrassGeometricLevelFour

/-!
# The universal four-torsion scheme is finite

The actual torsion equalizer of the universal smooth cubic is finite over its
coefficient base. Every geometric base change has sixteen points. Point count
is kept separate from scheme length: flat rank and reducedness remain to prove.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

/-- The full four-torsion equation of the original universal group. -/
def fourTorsion : Over parameterBase := GroupTorsionScheme.scheme universalGroup 4

/-- The universal four-torsion equation is finite over its coefficient parameter scheme. -/
instance fourTorsion_finite : IsFinite fourTorsion.hom :=
  WeierstrassIntegralChart.integralFourTorsion_isFinite smoothEquation
    smoothEquation_discriminant parameter_two_isUnit

/-- Finiteness holds after arbitrary base change, including nonreduced tests. -/
instance fourTorsion_baseChange_finite {T : Scheme} (g : T ⟶ parameterBase) :
    IsFinite (pullback.snd fourTorsion.hom g) := inferInstance

variable (K : Type) [Field K] [Algebra ParameterRing K]

/-- There are sixteen maps to the represented universal four-torsion on every geometric test. -/
theorem fourTorsion_geometric_maps_card [IsSepClosed K] :
    Nat.card (fieldTest K ⟶ fourTorsion) = 16 := by
  unfold fourTorsion
  rw [Nat.card_congr (GroupTorsionScheme.representation universalGroup 4 (fieldTest K))]
  exact geometricFourTorsion_card K

/-- The actual geometric fiber, retaining its possible infinitesimal structure. -/
def fourTorsionGeometricFiber : Scheme := pullback fourTorsion.hom (fieldTest K).hom

/-- Geometric fibers are finite schemes over the geometric field. -/
instance fourTorsionGeometricFiber_finite :
    IsFinite (pullback.snd fourTorsion.hom (fieldTest K).hom) := inferInstance

/-- The underlying geometric fiber has sixteen points; this is not a length assertion. -/
theorem fourTorsionGeometricFiber_card [IsAlgClosed K] :
    Nat.card (fourTorsionGeometricFiber K) = 16 := by
  let f := pullback.snd fourTorsion.hom (fieldTest K).hom
  have : IsLocallyArtinian (fieldTest K).left := inferInstanceAs
    (IsLocallyArtinian (Spec (.of K)))
  have : IsLocallyArtinian (fourTorsionGeometricFiber K) :=
    IsLocallyArtinian.of_locallyQuasiFinite f
  let e := (BaseChangeSectionEquiv.equiv fourTorsion.hom (fieldTest K).hom).symm.trans
    ((pointEquivClosedPoint f).trans
      ((Set.equivOfEq (closedPoints_eq_univ (X := fourTorsionGeometricFiber K))).trans
        (Equiv.Set.univ _)))
  exact (Nat.card_congr e).symm.trans (fourTorsion_geometric_maps_card K)

end FLT.Mazur.UniversalWeierstrass
