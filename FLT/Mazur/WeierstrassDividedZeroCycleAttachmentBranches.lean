/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalZeroBranchCharts
public import FLT.Mazur.WeierstrassDividedZeroExteriorNodeBranches
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# Start-zero attachment branches in the actual cyclic component family

Both original local pushout branches are identified with restrictions of
the actual cyclic component maps, including projective endpoint reversal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 1 (by omega))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "u" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : 0 + 1 + s ≤ n) hs (by omega))
local notation "G₁" => olderGlobalZeroFirstNode hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalZeroSecondNode hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- Reversal makes the right chart of cyclic component one the first actual conic branch. -/
@[reassoc] theorem zeroSplitCycleComponent_first_attachment_conic :
    ProjectiveLine.right K ≫ (Z 1).left =
      (E).hom ≫ (fullNodeConicParameterIso a c ha).hom ≫
        fullNodeFirstBranch a c ha ≫ G₁ ≫ transport := by
  have H : (Z 1).left = ProjectiveLine.endpointReversal K ≫
      (finalBranchComponent hπ data D s hs hk hp 0 0).left :=
    congrArg Over.Hom.left (zeroSplitCycleComponent_first hπ data D s hs hstart hk hp 0)
  rw [H]
  change ProjectiveLine.right K ≫ ProjectiveLine.endpointReversal K ≫
    (finalBranchComponent hπ data D s hs hk hp 0 0).left = _
  rw [ProjectiveLine.right_endpointReversal_assoc,
    finalBranchComponent_zero_first_left hπ data D s hs hstart hk hp,
    olderGlobalZeroFirstNode_conicBranch_assoc]

/-- The last cyclic component keeps its left chart and the opposite original conic branch. -/
@[reassoc] theorem zeroSplitCycleComponent_second_attachment_conic :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 2, by omega⟩).left =
      (E).hom ≫ (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
        fullNodeFirstBranch (-a) c (ha).neg ≫ G₂ ≫ transport := by
  have H : (Z ⟨2 * s + 2, by omega⟩).left =
      (finalBranchComponent hπ data D s hs hk hp 0 1).left :=
    congrArg Over.Hom.left (zeroSplitCycleComponent_second hπ data D s hs hstart hk hp 0)
  rw [H]
  rw [finalBranchComponent_zero_second_left hπ data D s hs hstart hk hp,
    olderGlobalZeroSecondNode_conicBranch_assoc]

/-- The first attachment's other branch is the exact localized original exterior component. -/
@[reassoc] theorem zeroSplitCycleComponent_first_attachment_exterior :
    NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ (Z 0).left =
      fullNodeSecondBranch a c ha ≫ G₁ ≫ transport := by
  rw [zeroSplitCycleComponent_exterior]
  change _ ≫ _ ≫ _ ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  rw [finalZeroExteriorComponent, zeroRetainedOrientedToGlobal_first_nodeBranch_assoc]

/-- The second attachment keeps the translated exterior branch and the original denominator. -/
@[reassoc] theorem zeroSplitCycleComponent_second_attachment_exterior :
    NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ (Z 0).left =
      fullNodeSecondBranch (-a) c (ha).neg ≫ G₂ ≫ transport := by
  rw [zeroSplitCycleComponent_exterior]
  change _ ≫ _ ≫ _ ≫ _ ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  rw [finalZeroExteriorComponent, zeroRetainedOrientedToGlobal_second_nodeBranch_assoc]

end FLT.Mazur.WeierstrassDividedDepth
