/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicIncidenceOrientation
public import FLT.Mazur.WeierstrassModificationXFullSecondNodeBranches

/-!
# The full ambient node origins are the existing ordered incidence sections

The two ambient intersection quotients give the same original fiber sections
as the conic constructions. Their ordering agrees with the original split
intersection, with slopes zero and -a respectively.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "F" => FiberCoordinate a c
local notation "O₀" => FullFirstFiberOpen a c
local notation "O₁" => FullSecondFiberOpen a c

/-- The first full ambient intersection section on the original fiber. -/
def fullFirstIncidencePoint : F →ₐ[R] R :=
  (fullFirstIncidenceEquiv a c ha).toAlgHom.comp
    ((Ideal.Quotient.mkₐ R
      (Ideal.span {algebraMap F O₀ (fiberT a c)} ⊔
        Ideal.span {algebraMap F O₀ (fiberConicFactor a c)})).comp
      (Algebra.algHom R F O₀))

/-- The second full ambient intersection section on the original fiber. -/
def fullSecondIncidencePoint : F →ₐ[R] R :=
  (fullSecondIncidenceEquiv a c ha).toAlgHom.comp
    ((Ideal.Quotient.mkₐ R
      (Ideal.span {algebraMap F O₁ (fiberT a c)} ⊔
        Ideal.span {algebraMap F O₁ (fiberConicFactor a c)})).comp
      (Algebra.algHom R F O₁))

/-- The original incidence coordinate vanishes at the first ambient intersection. -/
theorem fullFirstIncidencePoint_t : fullFirstIncidencePoint a c ha (fiberT a c) = 0 := by
  change fullFirstIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap F O₀ (fiberT a c))) = 0
  rw [fullFirstIncidenceEquiv_mk, fullFirstNodeEquiv_t, fullNodeOrigin_inverseT]

/-- The original slope at the first ambient intersection is zero. -/
theorem fullFirstIncidencePoint_v : fullFirstIncidencePoint a c ha (fiberV a c) = 0 := by
  change fullFirstIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap F O₀ (fiberV a c))) = 0
  rw [fullFirstIncidenceEquiv_mk, fullFirstNodeEquiv_v, fullNodeOrigin_inverseV]

/-- The original incidence coordinate vanishes at the second ambient intersection. -/
theorem fullSecondIncidencePoint_t : fullSecondIncidencePoint a c ha (fiberT a c) = 0 := by
  change fullSecondIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap F O₁ (fiberT a c))) = 0
  rw [fullSecondIncidenceEquiv_mk, fullSecondNodeEquiv_t, fullNodeOrigin_inverseT]

/-- The original slope at the second ambient intersection is -a. -/
theorem fullSecondIncidencePoint_v : fullSecondIncidencePoint a c ha (fiberV a c) = -a := by
  change fullSecondIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap F O₁ (fiberV a c))) = -a
  rw [fullSecondIncidenceEquiv_mk, fullSecondNodeEquiv_v, map_sub,
    fullNodeOrigin_inverseV, AlgHom.commutes, zero_sub]
  rfl

/-- The full ambient first section is the original first conic incidence section. -/
theorem fullFirstIncidencePoint_conic : fullFirstIncidencePoint a c ha =
    (conicFirstIncidencePoint a c ha).comp (fiberConicMap a c) := by
  apply fiber_hom_ext a c
  · simp only [AlgHom.comp_apply, fullFirstIncidencePoint_t, fiberConicMap_t,
      conicFirstIncidencePoint_t]
  · simp only [AlgHom.comp_apply, fullFirstIncidencePoint_v, fiberConicMap_v,
      conicFirstIncidencePoint_v]

/-- The full ambient second section is the original second conic incidence section. -/
theorem fullSecondIncidencePoint_conic : fullSecondIncidencePoint a c ha =
    (conicSecondIncidencePoint a c ha).comp (fiberConicMap a c) := by
  apply fiber_hom_ext a c
  · simp only [AlgHom.comp_apply, fullSecondIncidencePoint_t, fiberConicMap_t,
      conicSecondIncidencePoint_t]
  · simp only [AlgHom.comp_apply, fullSecondIncidencePoint_v, fiberConicMap_v,
      conicSecondIncidencePoint_v]

/-- The first ambient node origin is the first factor of the existing ordered intersection. -/
theorem fullFirstIncidencePoint_ordered : fullFirstIncidencePoint a c ha =
    (AlgHom.fst R R R).comp (fiberOrderedIntersectionMap a c ha) := by
  rw [fullFirstIncidencePoint_conic, conicFirstIncidencePoint_ordered]

/-- The second ambient node origin is the second factor of the existing ordered intersection. -/
theorem fullSecondIncidencePoint_ordered : fullSecondIncidencePoint a c ha =
    (AlgHom.snd R R R).comp (fiberOrderedIntersectionMap a c ha) := by
  rw [fullSecondIncidencePoint_conic, conicSecondIncidencePoint_ordered]

end FLT.Mazur.WeierstrassModificationX
