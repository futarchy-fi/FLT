/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle
public import FLT.Mazur.WeierstrassDividedFinalInitialParameterCharts

/-!
# Full initial affine charts in the positive-start equality cycle

The reversed first conic parameter, unchanged second conic parameter and
normalized original incidence line retain their complete scheme maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The first reversed cyclic component retains the complete original initial conic parameter. -/
@[reassoc] theorem positiveEqualityCycleComponent_initial_first_chart :
    ProjectiveLine.right K ≫ (Z 1).left =
      (conicZeroAffineIso c hc).hom ≫
        initialGlobalConicFirstParameter hπ data D (s + 1) hs hstart (by omega) := by
  have H := congrArg Over.Hom.left
    (positiveEqualityCycleComponent_first hπ data D s hs hstart hk hp 0)
  simp only [positiveEqualityBranchComponent_initial] at H
  erw [H]
  change ProjectiveLine.right K ≫ ProjectiveLine.endpointReversal K ≫
    finalInitialComponent hπ data D s hs hstart hk 0 = _
  rw [ProjectiveLine.right_endpointReversal_assoc, finalInitialComponent_first_left]

/-- The last cyclic component retains the complete opposite initial conic parameter. -/
@[reassoc] theorem positiveEqualityCycleComponent_initial_second_chart :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 3, by omega⟩).left =
      (conicZeroAffineIso c hc).hom ≫
        initialGlobalConicSecondParameter hπ data D (s + 1) hs hstart (by omega) := by
  have H := congrArg Over.Hom.left
    (positiveEqualityCycleComponent_second hπ data D s hs hstart hk hp 0)
  simp only [positiveEqualityBranchComponent_initial] at H
  erw [H]
  exact finalInitialComponent_second_left hπ data D s hs hstart hk

/-- The normalized original incidence line is the whole affine exterior chart. -/
@[reassoc] theorem positiveEqualityCycleComponent_incidence_chart :
    ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ (Z 0).left =
      initialGlobalIncidenceLine hπ data D (s + 1) hs hstart (by omega) := by
  rw [← initialExteriorOrientedIso_affine_assoc hπ data D (s + 1) hs hstart
    (by omega) (by omega), positiveEqualityCycleComponent_exterior,
    equalityInitialExteriorOverComponent_original, initialExteriorToGlobal_affine]

end FLT.Mazur.WeierstrassDividedDepth
