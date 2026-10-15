/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSplitGeometricContraction
public import FLT.Mazur.WeierstrassDividedEqualityGeometricContraction
public import FLT.Mazur.WeierstrassDividedOddCompleteClosedComparison
public import FLT.Mazur.WeierstrassDividedEvenCompleteClosedComparison
public import FLT.Mazur.PolygonPinchingClosedCubicMap
import all FLT.Mazur.WeierstrassDividedZeroCyclePushout
import all FLT.Mazur.PolygonPinchingClosedCubicMap
import all FLT.Mazur.PolygonPinchingCompleteClosedComparison
import all FLT.Mazur.WeierstrassDividedOddCompleteClosedComparison
import all FLT.Mazur.WeierstrassDividedEvenCompleteClosedComparison

/-!
# The complete closed cubic map is the original arithmetic contraction

Both parity comparisons commute with the original base-changed complete
cubic map, the entire closed-cubic isomorphism and the integral coefficient
morphism. This identifies the actual contractions on every component and node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs
local notation "g" => pullback.snd q f ≫ finiteGlobalContraction hπ data (s + 1) hs
variable (hstart : start = 0)
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
open PolygonInfinitesimalStages
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeClosedFiberInclusion

/-- The odd complete closed-fiber comparison retains the whole original arithmetic cubic map. -/
theorem oddCompleteClosedIso_originalCubic (hp : 2 * (start + s + 1) < depth) :
    (oddCompleteClosedIso hπ data D s hs hstart hp).hom ≫
      completeClosedPullbackCubicMap K (2 * s + 3) (by omega) 0 ≫
        (closedPointContractionCubicIso K (2 * s + 3) (by omega) 0).inv ≫
          (residueOneGonIso D hd).hom ≫ integralCoefficientMorphism W = g := by
  rw [oddCompleteClosedIso, pinchingCompleteClosedIso_closedCubic_assoc]
  simp only [Iso.hom_inv_id_assoc]
  exact (zeroSplitOriginalOneGonContraction_cubic hπ data D s hs hk hp hstart).symm

/-- The even comparison retains the same whole cubic map, including the depth-two case. -/
theorem evenCompleteClosedIso_originalCubic (hp : 2 * (start + s + 1) = depth) :
    (evenCompleteClosedIso hπ data D s hs hstart hp).hom ≫
      completeClosedPullbackCubicMap K (2 * s + 2) (by omega) 0 ≫
        (closedPointContractionCubicIso K (2 * s + 2) (by omega) 0).inv ≫
          (residueOneGonIso D hd).hom ≫ integralCoefficientMorphism W = g := by
  rw [evenCompleteClosedIso, pinchingCompleteClosedIso_closedCubic_assoc]
  simp only [Iso.hom_inv_id_assoc]
  exact (zeroEqualityOriginalOneGonContraction_cubic hπ data D s hs hk hp hstart).symm

end FLT.Mazur.WeierstrassDividedDepth
