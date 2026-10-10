/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeIncidenceOrientation
public import FLT.Mazur.WeierstrassModificationXFullNodeFunctions

/-!
# Original incidence sections from node and conic parameter origins

The origins in the actual parameter algebras compose to the original ordered
sections on every full fiber function. This seals the coordinate calculation
before its use in recursive global models.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "F" => FiberCoordinate a c
local notation "O₀" => FullFirstFiberOpen a c
local notation "O₁" => FullSecondFiberOpen a c

/-- The first full node origin agrees on all original fiber functions. -/
theorem fullFirstNodeOrigin_comp :
    (fullNodeOrigin a c ha).comp (fiberFullFirstNodeMap a c ha) =
      fullFirstIncidencePoint a c ha := by
  apply fiber_hom_ext a c
  · simp only [AlgHom.comp_apply, fiberFullFirstNodeMap_t,
      fullNodeOrigin_inverseT, fullFirstIncidencePoint_t]
  · simp only [AlgHom.comp_apply, fiberFullFirstNodeMap_v,
      fullNodeOrigin_inverseV, fullFirstIncidencePoint_v]

/-- The first conic parameter origin is its original incidence section. -/
theorem conicFirstParameterOrigin_comp :
    (conicParameterOrigin c).comp
      ((conicFirstParameterEquiv a c ha).symm.toAlgHom.comp
        (Algebra.algHom R (ConicCoordinate a c) (ConicFirstOpen a c))) =
      conicFirstIncidencePoint a c ha := by
  apply AlgHom.ext
  intro z
  exact (conicFirstIncidenceEquiv_mk a c ha
    (algebraMap (ConicCoordinate a c) (ConicFirstOpen a c) z)).symm

/-- The second full node origin agrees on all original fiber functions. -/
theorem fullSecondNodeOrigin_comp :
    (fullNodeOrigin (-a) c ha.neg).comp (fiberFullSecondNodeMap a c ha) =
      fullSecondIncidencePoint a c ha := by
  apply fiber_hom_ext a c
  · simp only [AlgHom.comp_apply, fiberFullSecondNodeMap_t,
      fullNodeOrigin_inverseT, fullSecondIncidencePoint_t]
  · simp only [AlgHom.comp_apply, fiberFullSecondNodeMap_v,
      fullNodeOrigin_inverseV, fullSecondIncidencePoint_v, map_sub, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, zero_sub]

/-- The second conic parameter origin is its original incidence section. -/
theorem conicSecondParameterOrigin_comp :
    (conicParameterOrigin c).comp
      ((conicSecondParameterEquiv a c ha).symm.toAlgHom.comp
        (Algebra.algHom R (ConicCoordinate a c) (ConicSecondOpen a c))) =
      conicSecondIncidencePoint a c ha := by
  apply AlgHom.ext
  intro z
  exact (conicSecondIncidenceEquiv_mk a c ha
    (algebraMap (ConicCoordinate a c) (ConicSecondOpen a c) z)).symm

end FLT.Mazur.WeierstrassModificationX
