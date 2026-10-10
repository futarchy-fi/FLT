/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeGeometry
public import FLT.Mazur.WeierstrassModificationXFullSecondNodeBranches

/-!
# Original fiber functions on the two full node charts

The algebra maps below induce the actual scheme charts. Incidence, slope and
the conic factor retain their original values and ordered orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "F" => FiberCoordinate a c
local notation "L₀" => FullNodeOpen a c
local notation "L₁" => FullNodeOpen (-a) c

/-- The original full fiber functions on the first actual node chart. -/
def fiberFullFirstNodeMap : F →ₐ[R] L₀ :=
  (fullFirstNodeEquiv a c ha).toAlgHom.comp (Algebra.algHom R F (FullFirstFiberOpen a c))

/-- The original full fiber functions on the second actual node chart. -/
def fiberFullSecondNodeMap : F →ₐ[R] L₁ :=
  (fullSecondNodeEquiv a c ha).toAlgHom.comp (Algebra.algHom R F (FullSecondFiberOpen a c))

/-- The first node retains the original incidence formula. -/
theorem fiberFullFirstNodeMap_t :
    fiberFullFirstNodeMap a c ha (fiberT a c) = fullNodeInverseT a c :=
  fullFirstNodeEquiv_t a c ha
/-- The first node retains the original slope formula. -/
theorem fiberFullFirstNodeMap_v :
    fiberFullFirstNodeMap a c ha (fiberV a c) = fullNodeInverseV a c :=
  fullFirstNodeEquiv_v a c ha
/-- The first node retains the original conic factor. -/
theorem fiberFullFirstNodeMap_conic :
    fiberFullFirstNodeMap a c ha (fiberConicFactor a c) =
      fullNodeQ a c * (fullNodeInverseV a c + algebraMap R L₀ a) :=
  fullFirstNodeEquiv_conic a c ha

/-- The second node retains the original incidence formula. -/
theorem fiberFullSecondNodeMap_t :
    fiberFullSecondNodeMap a c ha (fiberT a c) = fullNodeInverseT (-a) c :=
  fullSecondNodeEquiv_t a c ha
/-- The second node retains the original slope and its translation by a. -/
theorem fiberFullSecondNodeMap_v :
    fiberFullSecondNodeMap a c ha (fiberV a c) =
      fullNodeInverseV (-a) c - algebraMap R L₁ a :=
  fullSecondNodeEquiv_v a c ha
/-- The second node retains the original conic factor with its orientation. -/
theorem fiberFullSecondNodeMap_conic :
    fiberFullSecondNodeMap a c ha (fiberConicFactor a c) =
      fullNodeQ (-a) c * (fullNodeInverseV (-a) c + algebraMap R L₁ (-a)) :=
  fullSecondNodeEquiv_conic a c ha

/-- The first function map induces exactly the constructed ambient scheme chart. -/
theorem fullFirstNodeChart_eq_spec : fullFirstNodeChart a c ha =
    Spec.map (CommRingCat.ofHom (fiberFullFirstNodeMap a c ha).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- The second function map induces exactly the constructed ambient scheme chart. -/
theorem fullSecondNodeChart_eq_spec : fullSecondNodeChart a c ha =
    Spec.map (CommRingCat.ofHom (fiberFullSecondNodeMap a c ha).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassModificationX
