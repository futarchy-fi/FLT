/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedBoundaryTransition
public import FLT.Mazur.WeierstrassHorizontalLineLaurentComparison
public import FLT.Mazur.EllipticFiniteRetainedLaurentCharts
public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents

/-!
# Retained arithmetic Laurent charts on the full original horizontal lines

The original finite arithmetic punctures and full retained line maps agree
with their signed tangent factors at every later stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (m : ℕ) (hm : j + 1 + m ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "F" => ResidueField A
local notation "a" => WeierstrassDilatation.residueTangentUnit D

/-- The positive retained arithmetic chart has the actual inverse tangent line coordinate. -/
@[reassoc] theorem retainedPositiveLaurentChart_line :
    retainedPositiveLaurentChart A hπ data D j hj m hm hk0 (by omega) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (a)⁻¹).toRingHom) ≫
        ProjectiveLine.overlapLeft F ≫ olderGlobalMiddleFirstLine hπ data D j hj m hm hk0 hk := by
  rw [retainedPositiveLaurentChart, residueHorizontalRight_line hπ data D j hj hk0 hk]
  simp only [Category.assoc]
  rw [finiteRetainedBoundaryTensorChart_transition,
    WeierstrassSuccessiveX.residueLineToHorizontal_comp_assoc]
  rfl

/-- The negative retained arithmetic chart has the actual signed inverse tangent coordinate. -/
@[reassoc] theorem retainedNegativeLaurentChart_line :
    retainedNegativeLaurentChart A hπ data D j hj m hm hk0 (by omega) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        ProjectiveLine.overlapLeft F ≫ olderGlobalMiddleSecondLine hπ data D j hj m hm hk0 hk := by
  rw [retainedNegativeLaurentChart, residueHorizontalLeft_line hπ data D j hj hk0 hk]
  simp only [Category.assoc]
  rw [finiteRetainedBoundaryTensorChart_transition,
    WeierstrassSuccessiveX.residueLineToHorizontal_comp_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
