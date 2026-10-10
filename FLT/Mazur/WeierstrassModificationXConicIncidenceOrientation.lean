/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicIncidenceCharts
public import FLT.Mazur.WeierstrassModificationXFiberIntersectionSplit

/-!
# Matching the conic sections to the original ordered intersection

The two local conic incidence quotients give the same sections of the full
fiber as the first and second factors of its existing ordered intersection.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "C₀" => ConicCoordinate a c
local notation "F" => FiberCoordinate a c
local notation "O₀" => ConicFirstOpen a c
local notation "O₁" => ConicSecondOpen a c

/-- The first conic incidence section as an actual map on original conic functions. -/
def conicFirstIncidencePoint : C₀ →ₐ[R] R :=
  (conicFirstIncidenceEquiv a c ha).toAlgHom.comp
    ((Ideal.Quotient.mkₐ R (Ideal.span {algebraMap C₀ O₀ (conicT a c)})).comp
      (Algebra.algHom R C₀ O₀))

/-- The second conic incidence section as an actual map on original conic functions. -/
def conicSecondIncidencePoint : C₀ →ₐ[R] R :=
  (conicSecondIncidenceEquiv a c ha).toAlgHom.comp
    ((Ideal.Quotient.mkₐ R (Ideal.span {algebraMap C₀ O₁ (conicT a c)})).comp
      (Algebra.algHom R C₀ O₁))

/-- The first conic section has original incidence coordinate zero. -/
theorem conicFirstIncidencePoint_t : conicFirstIncidencePoint a c ha (conicT a c) = 0 := by
  change conicFirstIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap C₀ O₀ (conicT a c))) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]

/-- The second conic section has original incidence coordinate zero. -/
theorem conicSecondIncidencePoint_t : conicSecondIncidencePoint a c ha (conicT a c) = 0 := by
  change conicSecondIncidenceEquiv a c ha
    (Ideal.Quotient.mk _ (algebraMap C₀ O₁ (conicT a c))) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]

/-- The first conic section has original slope zero. -/
theorem conicFirstIncidencePoint_v : conicFirstIncidencePoint a c ha (conicV a c) = 0 :=
  conicFirstIncidenceEquiv_v a c ha

/-- The second conic section has original slope -a. -/
theorem conicSecondIncidencePoint_v : conicSecondIncidencePoint a c ha (conicV a c) = -a :=
  conicSecondIncidenceEquiv_v a c ha

/-- The existing ordered splitting evaluates original full fiber functions at 0 and -a. -/
theorem fiberIntersectionSplitEquiv_mk (q : F) :
    fiberIntersectionSplitEquiv a c ha (Ideal.Quotient.mk _ q) =
      ((fiberIncidenceMap a c q).eval 0, (fiberIncidenceMap a c q).eval (-a)) := by
  rfl

/-- The original ordered intersection as a map on the full fiber. -/
def fiberOrderedIntersectionMap : F →ₐ[R] R × R :=
  (fiberIntersectionSplitEquiv a c ha).toAlgHom.comp
    (Ideal.Quotient.mkₐ R (fiberIntersectionIdeal a c))

/-- The first conic incidence section agrees with the first original intersection factor. -/
theorem conicFirstIncidencePoint_ordered :
    (conicFirstIncidencePoint a c ha).comp (fiberConicMap a c) =
      (AlgHom.fst R R R).comp (fiberOrderedIntersectionMap a c ha) := by
  apply fiber_hom_ext a c
  · change conicFirstIncidencePoint a c ha (fiberConicMap a c (fiberT a c)) =
      (fiberIntersectionSplitEquiv a c ha (Ideal.Quotient.mk _ (fiberT a c))).1
    rw [fiberConicMap_t, conicFirstIncidencePoint_t, fiberIntersectionSplitEquiv_mk,
      fiberIncidenceMap_t]
    simp only [eval_zero]
  · change conicFirstIncidencePoint a c ha (fiberConicMap a c (fiberV a c)) =
      (fiberIntersectionSplitEquiv a c ha (Ideal.Quotient.mk _ (fiberV a c))).1
    rw [fiberConicMap_v, conicFirstIncidencePoint_v, fiberIntersectionSplitEquiv_mk,
      fiberIncidenceMap_v]
    simp only [eval_X]

/-- The second conic incidence section agrees with the second original intersection factor. -/
theorem conicSecondIncidencePoint_ordered :
    (conicSecondIncidencePoint a c ha).comp (fiberConicMap a c) =
      (AlgHom.snd R R R).comp (fiberOrderedIntersectionMap a c ha) := by
  apply fiber_hom_ext a c
  · change conicSecondIncidencePoint a c ha (fiberConicMap a c (fiberT a c)) =
      (fiberIntersectionSplitEquiv a c ha (Ideal.Quotient.mk _ (fiberT a c))).2
    rw [fiberConicMap_t, conicSecondIncidencePoint_t, fiberIntersectionSplitEquiv_mk,
      fiberIncidenceMap_t]
    simp only [eval_zero]
  · change conicSecondIncidencePoint a c ha (fiberConicMap a c (fiberV a c)) =
      (fiberIntersectionSplitEquiv a c ha (Ideal.Quotient.mk _ (fiberV a c))).2
    rw [fiberConicMap_v, conicSecondIncidencePoint_v, fiberIntersectionSplitEquiv_mk,
      fiberIncidenceMap_v]
    simp only [eval_X]

end FLT.Mazur.WeierstrassModificationX
