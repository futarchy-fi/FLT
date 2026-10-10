/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeBranchCoordinates
public import FLT.Mazur.WeierstrassModificationXFullNodeFunctions
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry

/-!
# The localized pinching branch is the original incidence component

The second node branch is identified as an exact scheme morphism on each
original tangent chart. The opposite chart retains its slope translation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (a c : K) (ha : IsUnit a)
local notation "s" => fullNodeNormalizedDenominator a c
local notation "L" => FullNodeOpen a c
local notation "B" => Localization.Away (PolygonNodeEqualizer.second s)

/-- The actual incidence restriction preserves the original field constants. -/
theorem fullNodeSecondRestriction_constant (k : K) :
    fullNodeSecondRestriction a c ha (algebraMap K L k) = algebraMap K B k := by
  rw [IsScalarTower.algebraMap_apply K (NodalFiber.Coordinate (0 : K)) L,
    fullNodeSecondRestriction_base, AlgEquiv.commutes, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply K K[X] B]

/-- Restriction to the incidence branch as a map over the original coefficient field. -/
def fullNodeSecondRestrictionAlg : L →ₐ[K] B where
  __ := fullNodeSecondRestriction a c ha
  commutes' := fullNodeSecondRestriction_constant a c ha

/-- The original incidence function vanishes on this branch. -/
theorem fullNodeSecondRestriction_inverseT :
    fullNodeSecondRestrictionAlg a c ha (fullNodeInverseT a c) = 0 := by
  change fullNodeSecondRestriction a c ha (fullNodeInverseT a c) = 0
  simp only [fullNodeInverseT, map_mul, fullNodeSecondRestriction_p, mul_zero, zero_mul]

/-- The original slope is the retained localized polynomial coordinate. -/
theorem fullNodeSecondRestriction_inverseV :
    fullNodeSecondRestrictionAlg a c ha (fullNodeInverseV a c) = algebraMap K[X] B X := by
  change fullNodeSecondRestriction a c ha (fullNodeInverseV a c) = _
  simp only [fullNodeInverseV, map_add, map_mul, map_pow, fullNodeSecondRestriction_p,
    fullNodeSecondRestriction_q, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero]

/-- On the first tangent chart the entire original incidence map is retained. -/
theorem fullNodeSecondRestriction_fiber :
    (fullNodeSecondRestrictionAlg a c ha).comp (fiberFullFirstNodeMap a c ha) =
      (Algebra.algHom K K[X] B).comp (fiberIncidenceMap a c) := by
  apply fiber_hom_ext
  · simp only [AlgHom.comp_apply, fiberFullFirstNodeMap_t,
      fullNodeSecondRestriction_inverseT, fiberIncidenceMap_t, map_zero]
  · simp only [AlgHom.comp_apply, fiberFullFirstNodeMap_v,
      fullNodeSecondRestriction_inverseV, fiberIncidenceMap_v]
    rfl

/-- The actual first node's incidence branch is the original localized incidence immersion. -/
@[reassoc] theorem fullNodeSecondBranch_firstChart :
    fullNodeSecondBranch a c ha ≫ fullFirstNodeChart a c ha =
      NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s) ≫
        fiberIncidenceImmersion a c := by
  rw [fullNodeSecondBranch_eq_spec, fullFirstNodeChart_eq_spec,
    NodeLocalDescent.branchOpen, fiberIncidenceImmersion, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : FiberCoordinate a c →ₐ[K] B =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (fullNodeSecondRestriction_fiber a c ha)

local notation "B'" => Localization.Away
  (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c))

/-- The opposite tangent chart retains the original slope translation by minus a. -/
theorem fullNodeSecondRestriction_secondFiber :
    (fullNodeSecondRestrictionAlg (-a) c ha.neg).comp (fiberFullSecondNodeMap a c ha) =
      (Algebra.algHom K K[X] B').comp
        ((aeval (X - C a)).comp (fiberIncidenceMap a c)) := by
  apply fiber_hom_ext
  · simp only [AlgHom.comp_apply, fiberFullSecondNodeMap_t,
      fullNodeSecondRestriction_inverseT, fiberIncidenceMap_t, map_zero]
  · simp only [AlgHom.comp_apply, fiberFullSecondNodeMap_v, map_sub,
      fullNodeSecondRestriction_inverseV, AlgHom.commutes, fiberIncidenceMap_v, aeval_X]
    change algebraMap K[X] B' X - algebraMap K B' a =
      algebraMap K[X] B' X - algebraMap K[X] B' (C a)
    exact congrArg (fun z => algebraMap K[X] B' X - z)
      (IsScalarTower.algebraMap_apply K K[X] B' a)

/-- The second actual node's incidence branch equals the original translated affine map. -/
@[reassoc] theorem fullNodeSecondBranch_secondChart :
    fullNodeSecondBranch (-a) c ha.neg ≫ fullSecondNodeChart a c ha =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
      Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        fiberIncidenceImmersion a c := by
  rw [fullNodeSecondBranch_eq_spec, fullSecondNodeChart_eq_spec,
    NodeLocalDescent.branchOpen, fiberIncidenceImmersion,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : FiberCoordinate a c →ₐ[K] B' =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (fullNodeSecondRestriction_secondFiber a c ha)

end FLT.Mazur.WeierstrassModificationX
