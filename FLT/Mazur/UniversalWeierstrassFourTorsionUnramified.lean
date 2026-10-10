/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteUnramifiedFieldLength
public import FLT.Mazur.UniversalWeierstrassFourTorsionFinite
public import FLT.Mazur.WeierstrassTorsionFormallyUnramified

/-!
# Unramified universal four-torsion and its geometric length

The full universal torsion equation is formally unramified. Its geometric
fibers are finite etale schemes of length sixteen. Flatness over the entire
coefficient base is a separate assertion and is not assumed here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

/-- The actual universal four-torsion equalizer is formally unramified. -/
instance fourTorsion_formallyUnramified : FormallyUnramified fourTorsion.hom := by
  apply WeierstrassIntegralChart.integralTorsion_formallyUnramified
  convert parameter_two_isUnit.mul parameter_two_isUnit using 1; norm_num

/-- Infinitesimal rigidity persists under arbitrary base change. -/
instance fourTorsion_baseChange_formallyUnramified {T : Scheme} (g : T ⟶ parameterBase) :
    FormallyUnramified (pullback.snd fourTorsion.hom g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

variable (K : Type) [Field K] [Algebra ParameterRing K]

/-- Every field fiber is etale, before any assertion about flatness over the base. -/
instance fourTorsionGeometricFiber_etale :
    Etale (pullback.snd fourTorsion.hom (fieldTest K).hom) :=
  FCurve.finiteUnramifiedField_etale _

/-- The actual field fibers have no infinitesimal thickening. -/
instance fourTorsionGeometricFiber_reduced : IsReduced (fourTorsionGeometricFiber K) :=
  FCurve.finiteUnramifiedField_reduced (pullback.snd fourTorsion.hom (fieldTest K).hom)

/-- The sixteen geometric points account for the full scheme-theoretic length. -/
theorem fourTorsionGeometricFiber_length [IsAlgClosed K] :
    FCurve.finiteSchemeLength (pullback.snd fourTorsion.hom (fieldTest K).hom) = 16 := by
  rw [FCurve.finiteUnramifiedField_length_eq_card]
  exact fourTorsionGeometricFiber_card K

/-- The finite-flat rank of each geometric fiber is sixteen. -/
theorem fourTorsionGeometricFiber_rank [IsAlgClosed K] (s : Spec (.of K)) :
    (pullback.snd fourTorsion.hom (fieldTest K).hom).finrank s = 16 := by
  rw [FCurve.finrank_eq_finiteSchemeLength, fourTorsionGeometricFiber_length]

end FLT.Mazur.UniversalWeierstrass
