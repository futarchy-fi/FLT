/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupSectionGenericCompatibility

/-!
# Integral subgroup sections cover the global closure

The generic point is dense in each individual point closure. Each integral
section has closed image and contains that generic point, so it contains the
whole point closure. The finite point-kernel cover then gives the global cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3)

/-- The dense generic point of one actual subgroup point closure. -/
def pointClosureGeneric (P : Index A W H j) : Spec (.of K) ⟶ pointClosureChart A W H j P :=
  Spec.map (CommRingCat.ofHom (AffineGenericClosure.inclusion
    (pointEvaluation A W H j P)).toRingHom)

/-- Injectivity of the coordinate inclusion gives density in the point closure. -/
theorem pointClosureGeneric_denseRange (P : Index A W H j) :
    DenseRange (pointClosureGeneric A W H j P) := by
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  change RingHom.ker (AffineGenericClosure.inclusion
    (pointEvaluation A W H j P)).toRingHom ≤ _
  rw [(RingHom.injective_iff_ker_eq_bot
    (AffineGenericClosure.inclusion (pointEvaluation A W H j P)).toRingHom).mp
    (AffineGenericClosure.inclusion_injective (pointEvaluation A W H j P))]
  exact bot_le

/-- The point closure's generic point is the original chart evaluation. -/
@[reassoc] theorem pointClosureGeneric_toChart (P : Index A W H j) :
    pointClosureGeneric A W H j P ≫ pointClosureToChart A W H j P =
      genericChartPoint A W H j P := by
  rw [pointClosureGeneric, pointClosureToChart, genericChartPoint, ← Spec.map_comp]
  rfl

/-- A closed integral section containing the generic point contains its entire point closure. -/
theorem pointClosure_mem_section (P : Index A W H j)
    (i : closureChart A W H j ⟶ gluedClosure A W H 1 2)
    (hi : genericChartPoint A W H j P ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P.1)
    (y : pointClosureChart A W H j P) :
    (pointClosureToChart A W H j P ≫ i) y ∈ Set.range (integralSection A W H P.1) := by
  refine (pointClosureGeneric_denseRange A W H j P).induction_on y ?_ ?_
  · exact (integralSection A W H P.1).isClosedEmbedding.isClosed_range.preimage
      (pointClosureToChart A W H j P ≫ i).continuous
  · intro x
    refine ⟨Spec.map (CommRingCat.ofHom (algebraMap A K)) x, ?_⟩
    change (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P.1) x =
      (pointClosureGeneric A W H j P ≫ pointClosureToChart A W H j P ≫ i) x
    rw [pointClosureGeneric_toChart_assoc, hi]

/-- Every point of the finite Y/Z subgroup closure lies on an actual integral subgroup section. -/
theorem integralSections_cover [Finite H] (x : gluedClosure A W H 1 2) :
    ∃ (P : H) (a : Spec (.of A)), integralSection A W H P a = x := by
  rcases closure_charts_cover A W H 1 2 x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · obtain ⟨P, y, rfl⟩ := pointClosure_charts_cover A W H 1 q
    obtain ⟨a, ha⟩ := pointClosure_mem_section A W H 1 P (closureLeft A W H 1 2)
      (genericChartPoint_left_section A W H P) y
    exact ⟨P.1, a, ha⟩
  · obtain ⟨P, y, rfl⟩ := pointClosure_charts_cover A W H 2 q
    obtain ⟨a, ha⟩ := pointClosure_mem_section A W H 2 P (closureRight A W H 1 2)
      (genericChartPoint_right_section A W H P) y
    exact ⟨P.1, a, ha⟩

end FLT.Mazur.EllipticSubgroupChart
