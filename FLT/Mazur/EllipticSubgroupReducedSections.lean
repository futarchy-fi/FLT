/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupHopfSpecialization
public import FLT.Mazur.EllipticReductionKernel

/-!
# Residue evaluations are the original smooth reductions

On points with nonsingular reduction, the actual integral section reduces to
the scheme point associated with the existing smooth-reduction homomorphism.
This comparison also applies at bad reduction when the individual point is smooth.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- Reduction of the ambient integral chart point is its normalized primitive reduction. -/
theorem integralChartPoint_residue_toCurve (j : Fin 3) (P : H)
    (hj : IsUnit ((primitiveLift A W P.1).coords j))
    (hP : SmoothReduction A W P.1) :
    Spec.map (CommRingCat.ofHom (residue A)) ≫ integralChartPoint A W H j P hj ≫
      closureAmbientChart A W H j ≫ integralCurveChart W j =
      (projectiveToIntegral W (smoothReductionHom A W ⟨P.1, hP⟩)).left := by
  let v := (primitiveLift A W P.1).normalize j hj
  have hv : v.coords j = 1 := PrimitiveLift.normalize_self _ j hj
  rw [projectiveToIntegral_chart W (smoothReductionHom A W ⟨P.1, hP⟩) j
    (residue A ∘ v.coords) (v.residue_equation A W)
    (by simp only [Function.comp_apply, hv, map_one])
    ((projectiveReduction_eq A W P.1 v).symm)]
  have he := congrArg (fun f : Coordinate W j →ₐ[A] ResidueField A => f.toRingHom)
    (v.chartEvaluation_residue A W j hv)
  have hc : integralChartPoint A W H j P hj ≫ closureAmbientChart A W H j =
      Spec.map (CommRingCat.ofHom (integralEvaluation A W H j P hj).toRingHom) := by
    rw [integralChartPoint, closureAmbientChart, ← Spec.map_comp]
    rfl
  rw [← Category.assoc (integralChartPoint A W H j P hj), hc]
  rw [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun f : Coordinate W j →+* ResidueField A =>
    Spec.map (CommRingCat.ofHom f) ≫ integralCurveChart W j) he

/-- The original integral section reduces to the existing smooth-reduction point. -/
theorem integralSection_residue_toCurve (P : H) (hP : SmoothReduction A W P.1) :
    Spec.map (CommRingCat.ofHom (residue A)) ≫ integralSection A W H P ≫
      closureToCurve A W H 1 2 =
      (projectiveToIntegral W (smoothReductionHom A W ⟨P.1, hP⟩)).left := by
  unfold integralSection
  split
  · rw [Category.assoc, closureLeft_toCurve]
    exact integralChartPoint_residue_toCurve A W H 1 P _ hP
  · rw [Category.assoc, closureRight_toCurve]
    exact integralChartPoint_residue_toCurve A W H 2 P _ hP

variable [Finite H]

/-- Residue evaluation on the actual global coordinate ring retains smooth reduction. -/
theorem globalClosureSpecializedEvaluation_smoothReduction (P : H)
    (hP : SmoothReduction A W P.1) :
    Spec.map (CommRingCat.ofHom
      (globalClosureSpecializedEvaluation A W H (ResidueField A) P).toRingHom) ≫
      (gluedClosure A W H 1 2).isoSpec.inv ≫ closureToCurve A W H 1 2 =
      (projectiveToIntegral W (smoothReductionHom A W ⟨P.1, hP⟩)).left := by
  rw [globalClosureSpecializedEvaluation_spec]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact integralSection_residue_toCurve A W H P hP

end FLT.Mazur.EllipticSubgroupChart
