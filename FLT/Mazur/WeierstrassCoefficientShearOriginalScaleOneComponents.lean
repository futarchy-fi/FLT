/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearOriginalRetainedLines
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentStructure
public import FLT.Mazur.WeierstrassDividedAdjacentComponentStructure
public import FLT.Mazur.ProjectiveLineRightChartExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearOriginalRetainedLines
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic

/-!
# Complete scale-one sheared components are the original ordered components

The independently glued scale-one components reconstruct the entire original
projective components. The comparison extends from their dense right charts
by separatedness, and therefore includes both affine origins and the conic chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (m : ℕ) (hm : j + 2 + m ≤ n)
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "ha" => Eq.trans (WeierstrassDilatation.residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent V))
local notation "hs" => show algebraMap R K (π ^ (start + j)) = 1 from by
  simp only [hk0, pow_zero, map_one]
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
variable (h3 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b3 = 0)
  (h4 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b4 = 0)
local notation "C₁" => coefficientShearScaleOneFirstComponent
  hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "C₂" => coefficientShearScaleOneSecondComponent
  hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "E" => coefficientShearGluedIso hπ data K 0 (j + 2 + m) hm
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 2 + m) hm)

/-- The independent first complete component reconstructs the original retained component. -/
@[reassoc] theorem coefficientShearScaleOneFirstComponent_original :
    C₁ ≫ (E).hom =
      adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext m hm := by
  apply ProjectiveLine.rightChart_hom_ext K p
  · rw [Category.assoc]
    change C₁ ≫ coefficientShearGluedStructure hπ data K 0 (j + 2 + m) hm = _
    rw [coefficientShearScaleOneFirstComponent_structure,
      adjacentZeroFirstComponent_structure]
  · rw [coefficientShearScaleOneFirstComponent_right_assoc,
      adjacentZeroFirstComponent_right]
    apply congrArg (ProjectiveLine.chartScaling K a⁻¹ ≫ ·)
    exact coefficientShearRetainedFirst_original hπ data D (j + 1) hjNext m hm
      (by omega) hkNext _ _ h3 h4 _

/-- The independent opposite component reconstructs the original signed retained component. -/
@[reassoc] theorem coefficientShearScaleOneSecondComponent_original :
    C₂ ≫ (E).hom =
      adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext m hm := by
  apply ProjectiveLine.rightChart_hom_ext K p
  · rw [Category.assoc]
    change C₂ ≫ coefficientShearGluedStructure hπ data K 0 (j + 2 + m) hm = _
    rw [coefficientShearScaleOneSecondComponent_structure,
      adjacentZeroSecondComponent_structure]
  · rw [coefficientShearScaleOneSecondComponent_right_assoc,
      adjacentZeroSecondComponent_right]
    apply congrArg (ProjectiveLine.chartScaling K (-a)⁻¹ ≫ ·)
    exact coefficientShearRetainedSecond_original hπ data D (j + 1) hjNext m hm
      (by omega) hkNext _ _ h3 h4 _

/-- The comparison retains the first member of the original ordered pair. -/
@[reassoc] theorem coefficientShearScaleOneFirstComponent_ordered :
    C₁ ≫ (E).hom = orderedAdjacentComponent hπ data D j hj hk hjNext hkNext m hm 0 := by
  rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext m hm hk0]
  exact coefficientShearScaleOneFirstComponent_original
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4

/-- The comparison retains the opposite member without changing its projective parameter. -/
@[reassoc] theorem coefficientShearScaleOneSecondComponent_ordered :
    C₂ ≫ (E).hom = orderedAdjacentComponent hπ data D j hj hk hjNext hkNext m hm 1 := by
  rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext m hm hk0]
  exact coefficientShearScaleOneSecondComponent_original
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4

end FLT.Mazur.WeierstrassDividedDepth
