/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearRetainedConicStage
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes

import all FLT.Mazur.WeierstrassCoefficientShearRetainedStage
import all FLT.Mazur.WeierstrassCoefficientShearRetainedConicStage
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Both full scale-one conic charts at the original zero start

Both entire affine parameter charts survive the equal-stage transport, giving
detection of the whole original scale-one conic at the first retained stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄) (j : Fin s)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "hj" => show j.val + 1 ≤ n from by omega
local notation "hjNext" => show j.val + 2 ≤ n from by omega
local notation "m" => s - (j.val + 1)
local notation "hs'" => show j.val + 2 + m ≤ n from by omega
local notation "e" => data ⟨j.val + 2, Nat.lt_succ_of_le hjNext⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "E" => coefficientShearStageIso hπ data Q r
  (j.val + 2 + m) (s + 1) hs' hs (by omega)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

variable (hjzero : start + j.val = 0)
local notation "C" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc j
local notation "d" => data ⟨j.val + 1, Nat.lt_succ_of_le hj⟩
local notation "gc" => coefficientShearAdjacent_coefficients hπ d e Q hp
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hscale" => show algebraMap R Q (π ^ (start + j.val)) = 1 from by
  rw [hjzero, pow_zero, map_one]
local notation "conic" => tensorShearScaleOneConicImmersion W (π ^ (start + j.val)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r hscale hp (gc).1 (gc).2.1 hr ≫
    coefficientShearRetainedTensorChart hπ data Q r (s + 1) hs j.castSucc
local notation "Z" => conicZeroAffineIso c (gc).2.2

/-- The first adjacent component retains the entire preceding conic parameter. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_scaleOne_first_left :
    ProjectiveLine.left Q ≫ C 0 =
      (Z).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic := by
  unfold coefficientShearResidueAdjacentComponent
  rw [dite_eq_right (by omega)]
  simp only [ite_true]
  rw [← Category.assoc, coefficientShearScaleOneFirstComponent_left]
  simp only [coefficientConicFirstParameter, Category.assoc]
  rw [coefficientShearRetainedTensorChart_stageIso]
  rfl

/-- The opposite adjacent component retains the full second conic parameter. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_scaleOne_second_left :
    ProjectiveLine.left Q ≫ C 1 =
      (Z).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic := by
  unfold coefficientShearResidueAdjacentComponent
  rw [dite_eq_right (by omega)]
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte]
  rw [← Category.assoc, coefficientShearScaleOneSecondComponent_left]
  simp only [coefficientConicSecondParameter, Category.assoc]
  rw [coefficientShearRetainedTensorChart_stageIso]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
