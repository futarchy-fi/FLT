/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearOriginalScaleOneComponents
public import FLT.Mazur.WeierstrassCoefficientShearOriginalFinalAdjacent
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
# Independent adjacent pairs in their original tangent order

Choose the independently glued positive-scale or scale-one component from the
actual preceding depth. Reconstruct both ordered maps, including their origins.
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
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (m : ℕ) (hm : j + 2 + m ≤ n)
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "ha" => Eq.trans (WeierstrassDilatation.residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent V))
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
variable (h3 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b3 = 0)
  (h4 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b4 = 0)
local notation "E" => coefficientShearGluedIso hπ data K 0 (j + 2 + m) hm

/-- Both independent complete adjacent components in the original branch order. -/
def coefficientShearRootOrderedAdjacent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (j + 2 + m) hm :=
  if h : 0 < start + j then
    let hs := WeierstrassDilatation.residue_scale_eq_zero D (start + j) h
    Fin.cases
      (coefficientShearAdjacentFirstComponent
        hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha)
      (fun _ => coefficientShearAdjacentSecondComponent
        hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha) i
  else
    let hs : algebraMap R K (π ^ (start + j)) = 1 := by
      rw [show start + j = 0 by omega, pow_zero, map_one]
    Fin.cases
      (coefficientShearScaleOneFirstComponent
        hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha)
      (fun _ => coefficientShearScaleOneSecondComponent
        hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha) i

include hk hkNext in
/-- Reconstruction recovers the original ordered pair for either preceding scale. -/
@[reassoc] theorem coefficientShearRootOrderedAdjacent_original (i : Fin 2) :
    coefficientShearRootOrderedAdjacent hπ data D j hj hjNext m hm h3 h4 i ≫ (E).hom =
      orderedAdjacentComponent hπ data D j hj hk hjNext hkNext m hm i := by
  unfold coefficientShearRootOrderedAdjacent
  split_ifs with h
  · fin_cases i
    · exact coefficientShearAdjacentFirstComponent_ordered
        hπ data D j hj h hk hjNext hkNext m hm h3 h4
    · exact coefficientShearAdjacentSecondComponent_ordered
        hπ data D j hj h hk hjNext hkNext m hm h3 h4
  · fin_cases i
    · exact coefficientShearScaleOneFirstComponent_ordered
        hπ data D j hj (by omega) hk hjNext hkNext m hm h3 h4
    · exact coefficientShearScaleOneSecondComponent_ordered
        hπ data D j hj (by omega) hk hjNext hkNext m hm h3 h4

include hk hkNext in
/-- The complete ordered pair preserves the actual coefficient structure. -/
@[reassoc] theorem coefficientShearRootOrderedAdjacent_structure (i : Fin 2) :
    coefficientShearRootOrderedAdjacent hπ data D j hj hjNext m hm h3 h4 i ≫
        coefficientShearGluedStructure hπ data K 0 (j + 2 + m) hm =
      ProjectiveLine.toBase K := by
  rw [coefficientShearGluedStructure,
    coefficientShearRootOrderedAdjacent_original_assoc
      hπ data D j hj hk hjNext hkNext m hm h3 h4,
    orderedAdjacentComponent_structure]

include hk hkNext in
/-- Each zero marking is the unchanged preceding original retained node. -/
@[reassoc] theorem coefficientShearRootOrderedAdjacent_zero_original (i : Fin 2) :
    ProjectiveLine.zero K ≫
        coefficientShearRootOrderedAdjacent hπ data D j hj hjNext m hm h3 h4 i ≫ (E).hom =
      retainedNodeSectionAt hπ data D (j + 2 + m) hm j (by omega) hk i := by
  rw [coefficientShearRootOrderedAdjacent_original
      hπ data D j hj hk hjNext hkNext m hm h3 h4, orderedAdjacentComponent_zero]

include hk hkNext in
/-- Each infinity marking is the matching original retained node at the next level. -/
@[reassoc] theorem coefficientShearRootOrderedAdjacent_infinity_original (i : Fin 2) :
    ProjectiveLine.infinity K ≫
        coefficientShearRootOrderedAdjacent hπ data D j hj hjNext m hm h3 h4 i ≫ (E).hom =
      retainedNodeSectionAt hπ data D (j + 2 + m) hm (j + 1) (by omega) hkNext i := by
  rw [coefficientShearRootOrderedAdjacent_original
      hπ data D j hj hk hjNext hkNext m hm h3 h4, orderedAdjacentComponent_infinity]

end FLT.Mazur.WeierstrassDividedDepth
