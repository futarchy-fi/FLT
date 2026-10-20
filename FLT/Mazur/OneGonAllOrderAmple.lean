/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonRootsOfUnitySubgroup
public import FLT.Mazur.OneGonIntegral
public import FLT.Mazur.SmoothFiniteSubgroupAmple
public import FLT.Mazur.GeneralizedCurveAmpleBaseChange
public import FLT.Mazur.TorusArithmeticCyclicity

/-!
# Ample cyclic roots of every order on the original one-gon

No characteristic or prime-power condition is imposed. The full Cartier
divisor is nonempty on the integral pinched curve, so its divisor line is ample.
Arithmetic cyclicity and ampleness persist on arbitrary scheme tests.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonSmoothing

open GeneralizedEllipticCurve FCurve

variable (K : Type) [Field K] (n : ℕ) [NeZero n]
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)

/-- Every positive-order roots-of-unity divisor on the original one-gon is ample. -/
theorem originalRootsOfUnitySubgroup_isAmple : (originalRootsOfUnitySubgroup K n).IsAmple := by
  let H := originalRootsOfUnitySubgroup K n
  let hI := (originalRootsOfUnitySubgroup_relativeCartier K n).1
  let _ : IsProper (E).curve.hom := (E).family.family.1
  let _ : IsIntegral (E).curve.left := OneGonIntegral.integral K
  let _ : IsFinite (H.ideal.subschemeι ≫ (E).curve.hom) := H.ideal_degree.1
  refine ⟨hI, (divisor_relativeAmple_iff_nonempty (E).curve.hom hI ?_).mpr
    (H.support_nonempty_of_positive (NeZero.pos n))⟩
  exact PolygonDimension.dimension K 1 Nat.zero_lt_one
    (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
    (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)

/-- Arithmetic Cartier cyclicity holds for the actual subgroup in every characteristic. -/
theorem originalRootsOfUnitySubgroup_isCyclic : (originalRootsOfUnitySubgroup K n).IsCyclic :=
  (E).torusRootsOfUnitySubgroup_isCyclic (rootsOfUnityTorusIso K) n

/-- All scheme tests retain the ample full subgroup divisor, including nonreduced tests. -/
theorem originalRootsOfUnitySubgroup_baseChange_isAmple {T : Scheme}
    (f : T ⟶ Spec (.of K)) : ((originalRootsOfUnitySubgroup K n).baseChange f).IsAmple :=
  (originalRootsOfUnitySubgroup_isAmple K n).baseChange f

/-- All scheme tests retain a cyclic subgroup with its full Cartier generator condition. -/
theorem originalRootsOfUnitySubgroup_baseChange_isCyclic {T : Scheme}
    (f : T ⟶ Spec (.of K)) : ((originalRootsOfUnitySubgroup K n).baseChange f).IsCyclic :=
  (originalRootsOfUnitySubgroup_isCyclic K n).baseChange _ f

end FLT.Mazur.OneGonSmoothing
