/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.WeierstrassDividedTerminalBranchIntersection
public import FLT.Mazur.WeierstrassDividedTerminalZeroBranchIntersection
public import FLT.Mazur.WeierstrassDividedFinalNodeFamily
public import FLT.Mazur.WeierstrassSuccessiveXResidueComponentPoints

/-!
# Original conic parameter origins in the final node family

The full parameter marking is the original retained ordered section, including
scale one. No change of node coordinates or orientation is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c)))

/-- Zero further retention is exactly the current original tensor chart. -/
theorem olderGlobalTensorChart_zero_retention :
    olderGlobalTensorChart hπ data K j hj 0 hj =
      globalSuccessiveTensorChart hπ data K j hj := by
  unfold olderGlobalTensorChart globalSuccessiveTensorChart
  congr 1

/-- The first positive-depth full parameter origin is the first retained section. -/
@[reassoc] theorem terminalConicFirstParameter_origin (hk0 : 0 < start + j) :
    o ≫ terminalConicFirstParameter hπ data D j hj hk0 hk =
      olderGlobalFirstSection hπ data D j hj 0 hj hk0 hk := by
  rw [terminalConicFirstParameter, Category.assoc,
    conicFirstParameterIso_origin_assoc, residueSuccessiveConicImmersion_eq_spec,
    ← Category.assoc, ← Spec.map_comp]
  rw [olderGlobalFirstSection, olderGlobalTensorChart_zero_retention]
  congr 1
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (residueFirstIncidencePoint_conic D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))

/-- The second positive-depth full parameter origin is the second retained section. -/
@[reassoc] theorem terminalConicSecondParameter_origin (hk0 : 0 < start + j) :
    o ≫ terminalConicSecondParameter hπ data D j hj hk0 hk =
      olderGlobalSecondSection hπ data D j hj 0 hj hk0 hk := by
  rw [terminalConicSecondParameter, Category.assoc,
    conicSecondParameterIso_origin_assoc, residueSuccessiveConicImmersion_eq_spec,
    ← Category.assoc, ← Spec.map_comp]
  rw [olderGlobalSecondSection, olderGlobalTensorChart_zero_retention]
  congr 1
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (residueSecondIncidencePoint_conic D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))

/-- The first scale-one full parameter origin is the first original retained section. -/
@[reassoc] theorem terminalZeroConicFirstParameter_origin (hk0 : start + j = 0) :
    o ≫ terminalZeroConicFirstParameter hπ data D j hj hk0 hk =
      olderGlobalZeroFirstSection hπ data D j hj 0 hj hk0 hk := by
  rw [← olderGlobalZeroFirstSection_conic, terminalZeroConicFirstParameter,
    Category.assoc, conicFirstParameterIso_origin_assoc]
  unfold olderGlobalZeroConic olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  rw [olderGlobalTensorChart_zero_retention]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The second scale-one origin retains the original opposite tangent marking. -/
@[reassoc] theorem terminalZeroConicSecondParameter_origin (hk0 : start + j = 0) :
    o ≫ terminalZeroConicSecondParameter hπ data D j hj hk0 hk =
      olderGlobalZeroSecondSection hπ data D j hj 0 hj hk0 hk := by
  rw [← olderGlobalZeroSecondSection_conic, terminalZeroConicSecondParameter,
    Category.assoc, conicSecondParameterIso_origin_assoc]
  unfold olderGlobalZeroConic olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  rw [olderGlobalTensorChart_zero_retention]
  simp only [Category.assoc, WeierstrassCurve.map]

end FLT.Mazur.WeierstrassDividedDepth
