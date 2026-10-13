/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFieldMarking
public import FLT.Mazur.GeometricPointCoverCriterion
public import FLT.Mazur.OddWeierstrassGeometricLevelThree
public import FLT.Mazur.WeierstrassGeometricThreeBasis

/-!
# Actual auxiliary bases exist over every geometric coefficient point

The explicit one- and three-torsion counts construct an injective field marking.
Its universal faithfulness lifts it to the actual auxiliary level scheme, so
that scheme covers the entire coefficient base, including characteristic two.
Etaleness of the auxiliary parameter map is a separate assertion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant)
open UniversalWeierstrass (Labels)

/-- Geometric coefficients have a basis of the original three-torsion points. -/
theorem exists_geometric_auxiliary_marking (K : Type) [Field K] [IsSepClosed K]
    [Algebra OddChartRing K] :
    ∃ φ : Labels 3 →* (fieldTest K ⟶ universalGroup), Function.Injective φ := by
  classical
  let _ : oddChartEquation.IsElliptic := ⟨oddChart_discriminant⟩
  obtain ⟨φ, hφ⟩ := WeierstrassGeometricThreeBasis.exists_injective_marking
    (oddChartEquation.map (algebraMap OddChartRing K)) (field_three_ne_zero K)
  let e := WeierstrassIntegralChart.integralAffinePointAddEquiv (K := K)
    oddChartEquation oddChart_discriminant
  let ψ := e.toAddMonoidHom.comp φ
  refine ⟨ψ.toMultiplicativeLeft, ?_⟩
  intro a b hab
  exact hφ (e.injective (congrArg Additive.ofMul hab))

/-- Each geometric coefficient point lifts to the constructed faithful-marking open. -/
theorem geometric_auxiliary_nonempty (K : Type) [Field K] [IsSepClosed K]
    [Algebra OddChartRing K] : Nonempty (fieldTest K ⟶ levelThree) := by
  obtain ⟨φ, hφ⟩ := exists_geometric_auxiliary_marking K
  exact ⟨AuxiliaryLevel.fieldFaithfulLift universalGroup (Labels 3) (fieldTest K).hom φ hφ⟩

/-- Every geometric point of the parameter scheme lifts through the original auxiliary map. -/
theorem auxiliary_geometric_lift (K : Type) [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ parameterBase) :
    ∃ q : Spec (.of K) ⟶ levelThree.left, q ≫ levelThree.hom = g := by
  obtain ⟨r, hr⟩ := Spec.map_surjective g
  let _ : Algebra OddChartRing K := r.hom.toAlgebra
  obtain ⟨q⟩ := geometric_auxiliary_nonempty K
  exact ⟨q.left, q.w.trans hr⟩

/-- The actual auxiliary scheme covers every coefficient parameter. -/
instance levelThree_surjective : Surjective levelThree.hom := by
  constructor
  intro s
  obtain ⟨_, y, hy⟩ := GeometricPointCoverCriterion.covers
    (fun _ : Unit ↦ levelThree.hom) (fun K _ _ g ↦ by
      obtain ⟨q, hq⟩ := auxiliary_geometric_lift K g
      exact ⟨(), q, hq⟩) s
  exact ⟨y, hy⟩

end FLT.Mazur.OddWeierstrassParameter
