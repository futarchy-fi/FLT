/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearOriginalAdjacentComponents
public import FLT.Mazur.WeierstrassDividedFinalAdjacentOverComponents
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentComponentStructure
public import FLT.Mazur.WeierstrassDividedAdjacentComponentStructure
public import FLT.Mazur.ProjectiveLineRightChartExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearOriginalAdjacentComponents
import all FLT.Mazur.WeierstrassCoefficientShearOriginalRetainedLines
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentComponents
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentComponentStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic

/-!
# Complete coefficient components in the final original normalization family

Transport the proved ordered comparison to the fixed final stage. Both signed
components are exactly the existing over-components, including their node endpoints.
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
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (m : ℕ) (hm : j + 2 + m ≤ n)
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "ha" => Eq.trans (WeierstrassDilatation.residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent V))
local notation "hs" => WeierstrassDilatation.residue_scale_eq_zero D (start + j) hk0
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
variable (h3 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b3 = 0)
  (h4 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b4 = 0)
local notation "C₁" => coefficientShearAdjacentFirstComponent
  hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "C₂" => coefficientShearAdjacentSecondComponent
  hπ data K 0 j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "E" => coefficientShearGluedIso hπ data K 0 (j + 2 + m) hm
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 2 + m) hm)

include hk hkNext in
/-- The original final-stage transport keeps the entire first sheared component. -/
@[reassoc] theorem coefficientShearAdjacentFirstComponent_final
    (s : ℕ) (hsFinal : s + 1 ≤ n) (hd : 2 * (start + s + 1) ≤ depth)
    (he : j + 2 + m = s + 1) (hjs : j < s) :
    C₁ ≫ (E).hom ≫ eqToHom (finiteGlobalTensorModel_index_congr hπ data K hm hsFinal he) =
      (finalAdjacentOverComponent hπ data D s hsFinal hd ⟨j, hjs⟩ 0).left := by
  rw [← Category.assoc, coefficientShearAdjacentFirstComponent_ordered
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4]
  change _ = finalAdjacentComponent hπ data D s hsFinal hd ⟨j, hjs⟩ 0
  have hm' : m = s - (j + 1) := by omega
  subst m
  rfl

include hk hkNext in
/-- The opposite original final over-component retains its full sheared projective parameter. -/
@[reassoc] theorem coefficientShearAdjacentSecondComponent_final
    (s : ℕ) (hsFinal : s + 1 ≤ n) (hd : 2 * (start + s + 1) ≤ depth)
    (he : j + 2 + m = s + 1) (hjs : j < s) :
    C₂ ≫ (E).hom ≫ eqToHom (finiteGlobalTensorModel_index_congr hπ data K hm hsFinal he) =
      (finalAdjacentOverComponent hπ data D s hsFinal hd ⟨j, hjs⟩ 1).left := by
  rw [← Category.assoc, coefficientShearAdjacentSecondComponent_ordered
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4]
  change _ = finalAdjacentComponent hπ data D s hsFinal hd ⟨j, hjs⟩ 1
  have hm' : m = s - (j + 1) := by omega
  subst m
  rfl

include hk hkNext in
/-- Zero of the first complete sheared component is the original preceding node. -/
@[reassoc] theorem coefficientShearAdjacentFirstComponent_original_zero :
    ProjectiveLine.zero K ≫ C₁ ≫ (E).hom =
      retainedNodeSectionAt hπ data D (j + 2 + m) hm j (by omega) hk 0 := by
  rw [coefficientShearAdjacentFirstComponent_ordered
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4, orderedAdjacentComponent_zero]

include hk hkNext in
/-- Infinity of the first complete component is the next original node, without an index shift. -/
@[reassoc] theorem coefficientShearAdjacentFirstComponent_original_infinity :
    ProjectiveLine.infinity K ≫ C₁ ≫ (E).hom =
      retainedNodeSectionAt hπ data D (j + 2 + m) hm (j + 1) (by omega) hkNext 0 := by
  rw [coefficientShearAdjacentFirstComponent_ordered
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4, orderedAdjacentComponent_infinity]

include hk hkNext in
/-- Zero of the opposite component retains the other preceding ordered node. -/
@[reassoc] theorem coefficientShearAdjacentSecondComponent_original_zero :
    ProjectiveLine.zero K ≫ C₂ ≫ (E).hom =
      retainedNodeSectionAt hπ data D (j + 2 + m) hm j (by omega) hk 1 := by
  rw [coefficientShearAdjacentSecondComponent_ordered
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4, orderedAdjacentComponent_zero]

include hk hkNext in
/-- Infinity of the opposite component is its matching original next node. -/
@[reassoc] theorem coefficientShearAdjacentSecondComponent_original_infinity :
    ProjectiveLine.infinity K ≫ C₂ ≫ (E).hom =
      retainedNodeSectionAt hπ data D (j + 2 + m) hm (j + 1) (by omega) hkNext 1 := by
  rw [coefficientShearAdjacentSecondComponent_ordered
    hπ data D j hj hk0 hk hjNext hkNext m hm h3 h4, orderedAdjacentComponent_infinity]

end FLT.Mazur.WeierstrassDividedDepth
