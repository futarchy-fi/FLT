/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorConicCharts
public import FLT.Mazur.WeierstrassDividedOlderSplitNodeBranches
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion
public import FLT.Mazur.WeierstrassDividedFiniteLineReciprocals
public import FLT.Mazur.WeierstrassSuccessiveXMiddleScaledDescent
public import FLT.Mazur.ProjectiveLineScaledAffineOverlap

/-!
# The original retained conic punctures on the interior cyclic components

Both punctures of every earlier successive conic keep their actual component
labels. Endpoint reversal on the first chain and the negative parameter on
the opposite node are accounted for in the complete morphism equalities.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j.val + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "C" => olderGlobalMiddleConic hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)
local notation "P₁" => olderGlobalMiddleConicFirstParameter hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)
local notation "P₂" => olderGlobalMiddleConicSecondParameter hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)

/-- The full first conic parameter is the right chart of the original interior component. -/
theorem interiorConicFirstParameter_cycle :
    (conicZeroAffineIso c hc).hom ≫ P₁ ≫ transport =
      ProjectiveLine.right K ≫ (Z ⟨j.val + 2, by omega⟩).left := by
  rw [positiveEqualityCycleComponent_interior_first_conic_chart,
    olderGlobalResidueFirstNode_conicBranch_assoc]

/-- The opposite full parameter keeps its actual cyclic orientation after sign cancellation. -/
theorem interiorConicSecondParameter_cycle :
    (conicZeroAffineIso c hc).hom ≫ P₂ ≫ transport =
      ProjectiveLine.left K ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left := by
  apply (cancel_epi (ProjectiveLine.chartScalingIso K (-1)).hom).mp
  change ProjectiveLine.chartScaling K (-1) ≫ _ = ProjectiveLine.chartScaling K (-1) ≫ _
  rw [← middleNode_negativeParameter_eq_scaling]
  rw [positiveEqualityCycleComponent_interior_second_conic_chart,
    olderGlobalResidueSecondNode_conicBranch_assoc]

/-- The first actual conic puncture retains the reversed first-chain component label. -/
theorem interiorConicFirstPuncture_cycle :
    Spec.map (CommRingCat.ofHom
        (conicPuncturedFirst (W.map (residue R)) c hc).toRingHom) ≫ C ≫ transport =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.right K ≫
        (Z ⟨j.val + 2, by omega⟩).left := by
  have h := congrArg (ProjectiveLine.overlapLeft K ≫ ·)
    (interiorConicFirstParameter_cycle hπ data D s hs hstart hk hp j)
  rw [← Category.assoc, conicZeroAffineIso_puncture] at h
  rw [conicPuncturedFirst_spec c hc (W.map (residue R)) (residue_tangent_isUnit D)]
  simpa only [olderGlobalMiddleConicFirstParameter,
    WeierstrassCurve.map_a₁, Category.assoc] using h

/-- The opposite actual puncture retains the second-chain label and original conic coordinate. -/
theorem interiorConicSecondPuncture_cycle :
    Spec.map (CommRingCat.ofHom
        (conicPuncturedSecond (W.map (residue R)) c hc).toRingHom) ≫ C ≫ transport =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (Z ⟨2 * s + 2 - j.val, by omega⟩).left := by
  have h := congrArg (ProjectiveLine.overlapLeft K ≫ ·)
    (interiorConicSecondParameter_cycle hπ data D s hs hstart hk hp j)
  rw [← Category.assoc, conicZeroAffineIso_puncture] at h
  rw [conicPuncturedSecond_spec c hc (W.map (residue R)) (residue_tangent_isUnit D)]
  simpa only [olderGlobalMiddleConicSecondParameter,
    WeierstrassCurve.map_a₁, Category.assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
