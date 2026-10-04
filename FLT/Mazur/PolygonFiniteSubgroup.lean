/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSubgroupIdeal
public import FLT.Mazur.PolygonGeneralizedCurve
public import FLT.Mazur.PolygonCyclicDivisor
public import FLT.Mazur.PolygonDivisorDegree

/-!
# The finite subgroup on the standard polygon

The actual all-one divisor supplies a rank-n subgroup of the full DR polygon.
Its ideal is the previously constructed relative effective Cartier divisor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonFiniteSubgroup
open PolygonPinching PolygonBoundaryDivisor GeneralizedEllipticCurve
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual cyclic divisor is a finite subgroup of the full DR polygon. -/
def subgroup : (PolygonGeneralizedCurve.curve K n hn p q h).FiniteSubgroup n := by
  let := polygon_lfp K n hn p q h
  let := PolygonCyclicDivisor.commGrpObj K n p hn q h
  exact
    { carrier := PolygonCyclicDivisor.divisor K n p
      inclusion := PolygonCyclicDivisor.inclusion K n p hn q h
      closed := PolygonCyclicDivisor.inclusion_closed K n p hn q h
      degree := PolygonDivisorDegree.degree K n p hn q h (fun _ ↦ 1) }

/-- The general subgroup map is the existing divisor closed immersion. -/
@[simp]
theorem curveMap : (subgroup K n p hn q h).curveMap.left =
    (ideal K n p (fun _ ↦ 1)).subschemeι := by
  let := polygon_lfp K n hn p q h
  exact PolygonCyclicDivisor.inclusion_smoothMap K n p hn q h

/-- The subgroup's intrinsic ideal is precisely the all-one boundary ideal. -/
@[simp]
theorem subgroup_ideal : (subgroup K n p hn q h).ideal = ideal K n p (fun _ ↦ 1) := by
  rw [FiniteSubgroup.ideal, curveMap, Scheme.IdealSheafData.ker_subschemeι]

/-- This actual subgroup is a relative effective Cartier divisor. -/
theorem relativeCartier :
    FCurve.RelativeEffectiveCartier C.hom (subgroup K n p hn q h).ideal := by
  rw [subgroup_ideal]
  exact cartier K n p hn q h (fun _ ↦ 1)

end FLT.Mazur.PolygonFiniteSubgroup
