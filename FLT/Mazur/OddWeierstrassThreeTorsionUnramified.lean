/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteUnramifiedFieldLength
public import FLT.Mazur.OddWeierstrassThreeTorsionFinite
public import FLT.Mazur.WeierstrassTorsionFormallyUnramified

/-!
# Unramified universal three-torsion and its geometric length

The full universal torsion equation is formally unramified. Its geometric
fibers are finite etale schemes of length nine. Flatness over the entire
coefficient base is a separate assertion and is not assumed here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant
  oddChart_three_isUnit)

/-- The actual universal three-torsion equalizer is formally unramified. -/
instance threeTorsion_formallyUnramified : FormallyUnramified threeTorsion.hom := by
  apply WeierstrassIntegralChart.integralTorsion_formallyUnramified
  exact oddChart_three_isUnit

/-- Infinitesimal rigidity persists under arbitrary base change. -/
instance threeTorsion_baseChange_formallyUnramified {T : Scheme} (g : T ⟶ parameterBase) :
    FormallyUnramified (pullback.snd threeTorsion.hom g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

variable (K : Type) [Field K] [Algebra OddChartRing K]

/-- Every field fiber is etale, before any assertion about flatness over the base. -/
instance threeTorsionGeometricFiber_etale :
    Etale (pullback.snd threeTorsion.hom (fieldTest K).hom) :=
  FCurve.finiteUnramifiedField_etale _

/-- The actual field fibers have no infinitesimal thickening. -/
instance threeTorsionGeometricFiber_reduced : IsReduced (threeTorsionGeometricFiber K) :=
  FCurve.finiteUnramifiedField_reduced (pullback.snd threeTorsion.hom (fieldTest K).hom)

/-- The nine geometric points account for the full scheme-theoretic length. -/
theorem threeTorsionGeometricFiber_length [IsAlgClosed K] :
    FCurve.finiteSchemeLength (pullback.snd threeTorsion.hom (fieldTest K).hom) = 9 := by
  rw [FCurve.finiteUnramifiedField_length_eq_card]
  exact threeTorsionGeometricFiber_card K

/-- The finite-flat rank of each geometric fiber is nine. -/
theorem threeTorsionGeometricFiber_rank [IsAlgClosed K] (s : Spec (.of K)) :
    (pullback.snd threeTorsion.hom (fieldTest K).hom).finrank s = 9 := by
  rw [FCurve.finrank_eq_finiteSchemeLength, threeTorsionGeometricFiber_length]

end FLT.Mazur.OddWeierstrassParameter
