/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentStructure
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentComponentRootChange
public import FLT.Mazur.ProjectiveLineRightChartExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineRootChange
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic

/-!
# Actual root exchange on complete scale-one projective components

The independently glued first and opposite projective lines exchange under
root change. Separatedness extends the proved original line comparison over
both affine origins and the whole conic chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
include hj hjNext
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "e" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
include h3 h4
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := start + j)
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
variable (t : S) (b : Sˣ)
  (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "C₁" => coefficientShearScaleOneFirstComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "C₂" => coefficientShearScaleOneSecondComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "D₁" => coefficientShearScaleOneFirstComponent
  hπ data S t j hj hjNext m hm hs hp h3 h4 ht b hb
local notation "D₂" => coefficientShearScaleOneSecondComponent
  hπ data S t j hj hjNext m hm hs hp h3 h4 ht b hb
local notation "changeRoot" => coefficientShearRootChange hπ data S r t (j + 2 + m) hm
local notation "gt" => coefficientShearGluedStructure hπ data S t (j + 2 + m) hm

include hrt in
/-- Actual root exchange identifies the whole first projective component with its companion. -/
@[reassoc] theorem coefficientShearScaleOneFirstComponent_rootChange :
    C₁ ≫ (changeRoot).hom = D₂ := by
  let _ : IsSeparated gt := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext S gt
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearScaleOneFirstComponent_structure,
      coefficientShearScaleOneSecondComponent_structure]
  · rw [coefficientShearScaleOneFirstComponent_right_assoc,
      coefficientShearScaleOneSecondComponent_right,
      coefficientShearRootChange_retainedFirst hπ data S r t (j + 2 + m) (j + 1) hm
        (by omega) hsNext hp h3 h4 hr ht hrt]
    rw [coefficientShearAdjacent_oppositeUnits S r a ha t b hb hrt]

include hrt in
/-- The entire opposite projective component returns to the independently glued first one. -/
@[reassoc] theorem coefficientShearScaleOneSecondComponent_rootChange :
    C₂ ≫ (changeRoot).hom = D₁ := by
  let _ : IsSeparated gt := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext S gt
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearScaleOneSecondComponent_structure,
      coefficientShearScaleOneFirstComponent_structure]
  · rw [coefficientShearScaleOneSecondComponent_right_assoc,
      coefficientShearScaleOneFirstComponent_right,
      coefficientShearRootChange_retainedSecond hπ data S r t (j + 2 + m) (j + 1) hm
        (by omega) hsNext hp h3 h4 hr ht hrt]
    have hUnits := coefficientShearAdjacent_oppositeUnits S r a ha t b hb hrt
    have hu' : -a = b := by rw [← hUnits, neg_neg]
    rw [hu']

end FLT.Mazur.WeierstrassDividedDepth
