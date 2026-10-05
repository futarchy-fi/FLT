/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupSectionGenericCompatibility

/-!
# Distinct subgroup points give distinct generic sections

The actual overlap pullback detects a nonzero transition denominator. Thus
coincident generic sections can be compared in a single coordinate chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- A generic chart morphism determines its normalized coordinates and its subgroup point. -/
theorem genericChartPoint_injective (j : Fin 3) :
    Function.Injective (genericChartPoint A W H j) := by
  intro P Q h
  have he := Spec.map_injective h
  apply coordinates_injective A W H j
  funext i
  have hc := congrArg (fun f : CommRingCat.of (Closure A W H j) ⟶ CommRingCat.of K =>
    f.hom (closureCoord A W H j i)) he
  change pointEvaluation A W H j P (closureCoord A W H j i) =
    pointEvaluation A W H j Q (closureCoord A W H j i) at hc
  simpa only [closureCoord, pointEvaluation_coord] using hc

/-- A generic point factoring through the overlap has nonzero opposite coordinate. -/
theorem genericChartPoint_overlap_nonzero (j k : Fin 3) (P : Index A W H j)
    (q : Spec (.of K) ⟶ closureIntersection A W H j k)
    (hq : q ≫ closureToLeft A W H j k = genericChartPoint A W H j P) :
    coordinates A W H j P k ≠ 0 := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective q
  rw [closureToLeft, genericChartPoint, ← Spec.map_comp] at hq
  have he := Spec.map_injective hq
  have hu := (IsLocalization.Away.algebraMap_isUnit
    (closureCoord A W H j k) (S := LocalizedClosure A W H j k)).map f.hom
  have hv := congrArg (fun g : CommRingCat.of (Closure A W H j) ⟶ CommRingCat.of K =>
    g.hom (closureCoord A W H j k)) he
  have hn := (hv ▸ hu).ne_zero
  change pointEvaluation A W H j P (closureCoord A W H j k) ≠ 0 at hn
  simpa only [closureCoord, pointEvaluation_coord] using hn

/-- Coincident points in opposite charts represent the same subgroup point. -/
theorem genericChartPoint_mixed_injective (j k : Fin 3)
    (P : Index A W H j) (Q : Index A W H k)
    (h : genericChartPoint A W H j P ≫ closureLeft A W H j k =
      genericChartPoint A W H k Q ≫ closureRight A W H j k) : P.1 = Q.1 := by
  let pb := closureChart_isPullback A W H j k
  let q := pb.lift (genericChartPoint A W H j P) (genericChartPoint A W H k Q) h
  have hn := genericChartPoint_overlap_nonzero A W H j k P q (pb.lift_fst _ _ h)
  let R : OverlapIndex A W H j k := ⟨P, by simpa only [coordinateMap_coord] using hn⟩
  have he := (genericChartPoint_overlap A W H j k R).symm.trans h
  have hi := genericChartPoint_injective A W H k ((cancel_mono _).mp he)
  exact congrArg Subtype.val hi

/-- The actual integral section restricted to the generic point of the base. -/
def genericSection (P : H) : Spec (.of K) ⟶ gluedClosure A W H 1 2 :=
  Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralSection A W H P

/-- Distinct subgroup points remain distinct as morphisms into the glued generic closure. -/
theorem genericSection_injective : Function.Injective (genericSection A W H) := by
  intro P Q h
  classical
  by_cases hp : IsUnit ((primitiveLift A W P.1).coords 1)
  · let p := integralIndex A W H 1 P hp
    have ep := genericChartPoint_left_section A W H p
    by_cases hq : IsUnit ((primitiveLift A W Q.1).coords 1)
    · let q := integralIndex A W H 1 Q hq
      have eq := genericChartPoint_left_section A W H q
      have he := ep.trans (h.trans eq.symm)
      exact congrArg Subtype.val
        (genericChartPoint_injective A W H 1 ((cancel_mono _).mp he))
    · let q := integralIndex A W H 2 Q
        (((primitiveLift A W Q.1).unit_Y_or_Z A W).resolve_left hq)
      exact genericChartPoint_mixed_injective A W H 1 2 p q
        (ep.trans (h.trans (genericChartPoint_right_section A W H q).symm))
  · let p := integralIndex A W H 2 P
      (((primitiveLift A W P.1).unit_Y_or_Z A W).resolve_left hp)
    have ep := genericChartPoint_right_section A W H p
    by_cases hq : IsUnit ((primitiveLift A W Q.1).coords 1)
    · let q := integralIndex A W H 1 Q hq
      exact (genericChartPoint_mixed_injective A W H 1 2 q p
        ((genericChartPoint_left_section A W H q).trans (h.symm.trans ep.symm))).symm
    · let q := integralIndex A W H 2 Q
        (((primitiveLift A W Q.1).unit_Y_or_Z A W).resolve_left hq)
      have he := ep.trans (h.trans (genericChartPoint_right_section A W H q).symm)
      exact congrArg Subtype.val
        (genericChartPoint_injective A W H 2 ((cancel_mono _).mp he))

end FLT.Mazur.EllipticSubgroupChart
