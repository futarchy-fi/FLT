/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassThreeTorsionFinite
public import FLT.Mazur.OddWeierstrassGeometricLevelThree

/-!
# The universal three-torsion scheme is finite

The actual torsion equalizer of the universal smooth cubic is finite over its
coefficient base. Every geometric base change has nine points. Point count
is kept separate from scheme length: flat rank and reducedness remain to prove.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant
  oddChart_three_isUnit)

/-- The full three-torsion equation of the original universal group. -/
def threeTorsion : Over parameterBase := GroupTorsionScheme.scheme universalGroup 3

/-- The universal three-torsion equation is finite over its coefficient parameter scheme. -/
instance threeTorsion_finite : IsFinite threeTorsion.hom :=
  WeierstrassIntegralChart.integralThreeTorsion_isFinite oddChartEquation
    oddChart_discriminant oddChart_three_isUnit

/-- Finiteness holds after arbitrary base change, including nonreduced tests. -/
instance threeTorsion_baseChange_finite {T : Scheme} (g : T ⟶ parameterBase) :
    IsFinite (pullback.snd threeTorsion.hom g) := inferInstance

variable (K : Type) [Field K] [Algebra OddChartRing K]

/-- There are nine maps to the represented universal three-torsion on every geometric test. -/
theorem threeTorsion_geometric_maps_card [IsSepClosed K] :
    Nat.card (fieldTest K ⟶ threeTorsion) = 9 := by
  unfold threeTorsion
  rw [Nat.card_congr (GroupTorsionScheme.representation universalGroup 3 (fieldTest K))]
  exact geometricThreeTorsion_card K

/-- The actual geometric fiber, retaining its possible infinitesimal structure. -/
def threeTorsionGeometricFiber : Scheme := pullback threeTorsion.hom (fieldTest K).hom

/-- Geometric fibers are finite schemes over the geometric field. -/
instance threeTorsionGeometricFiber_finite :
    IsFinite (pullback.snd threeTorsion.hom (fieldTest K).hom) := inferInstance

/-- The underlying geometric fiber has nine points; this is not a length assertion. -/
theorem threeTorsionGeometricFiber_card [IsAlgClosed K] :
    Nat.card (threeTorsionGeometricFiber K) = 9 := by
  let f := pullback.snd threeTorsion.hom (fieldTest K).hom
  have : IsLocallyArtinian (fieldTest K).left := inferInstanceAs
    (IsLocallyArtinian (Spec (.of K)))
  have : IsLocallyArtinian (threeTorsionGeometricFiber K) :=
    IsLocallyArtinian.of_locallyQuasiFinite f
  let e := (BaseChangeSectionEquiv.equiv threeTorsion.hom (fieldTest K).hom).symm.trans
    ((pointEquivClosedPoint f).trans
      ((Set.equivOfEq (closedPoints_eq_univ (X := threeTorsionGeometricFiber K))).trans
        (Equiv.Set.univ _)))
  exact (Nat.card_congr e).symm.trans (threeTorsion_geometric_maps_card K)

end FLT.Mazur.OddWeierstrassParameter
