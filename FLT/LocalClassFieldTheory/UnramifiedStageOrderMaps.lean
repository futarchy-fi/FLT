/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOpenStages
public import FLT.LocalClassFieldTheory.UnramifiedOrderTower

/-!
# Order compatibility between canonical unramified stages

The tower theorem applies to the canonical integral closures and to the
actual inclusion maps of the constructed degree-indexed fields.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "E[" n "]" => unramifiedFiniteStage R K C n
local notation "S[" n "]" => integralClosure R (E[n])

attribute [local instance] stageDvr stageUnramified stageFractionRing stageFinite stageLocalHom

/-- Inclusion of multiplicative coefficient groups between constructed stages. -/
def unramifiedStageUnitMap {n m : UnramifiedIndex} (h : n ≤ m) : (E[n])ˣ →* (E[m])ˣ :=
  Units.map (IntermediateField.inclusion (unramifiedFiniteStage_monotone R K C h)).toMonoidHom

set_option synthInstance.maxHeartbeats 100000 in
-- Resolve the compatible canonical integral-closure scalar towers.
set_option maxHeartbeats 600000 in
-- Canonical integral closures carry several compatible scalar-tower instances.
/-- The canonical integer order commutes with the actual finite-stage coefficient inclusion. -/
theorem unramifiedStageOrder_natural {n m : UnramifiedIndex} (h : n ≤ m) (x : (E[n])ˣ) :
    discreteOrder (S[m]) (E[m]) (unramifiedStageUnitMap R K C h x) =
      discreteOrder (S[n]) (E[n]) x := by
  let hnm := unramifiedFiniteStage_monotone R K C h
  let : Algebra (E[n]) (E[m]) := (Subsemiring.inclusion hnm).toAlgebra
  let : IsScalarTower K (E[n]) (E[m]) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R (E[n]) (E[m]) := IsScalarTower.of_algebraMap_eq' rfl
  let j := (IsScalarTower.toAlgHom R (E[n]) (E[m])).mapIntegralClosure
  let : Algebra (S[n]) (S[m]) := j.toRingHom.toAlgebra
  let : Algebra (S[n]) (E[m]) :=
    ((algebraMap (E[n]) (E[m])).comp (algebraMap (S[n]) (E[n]))).toAlgebra
  let : IsScalarTower (S[n]) (E[n]) (E[m]) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S[n]) (S[m]) (E[m]) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R (S[n]) (E[m]) := IsScalarTower.of_algebraMap_eq' rfl
  exact discreteOrder_unramified_tower R (S[n]) (S[m]) (E[n]) (E[m]) x

end LocalClassFieldTheory
