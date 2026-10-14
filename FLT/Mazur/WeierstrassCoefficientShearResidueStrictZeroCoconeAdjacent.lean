/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeLines
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeLines
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentPositiveLeft
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentScaleOneLeft
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentFullRight
public import FLT.Mazur.WeierstrassCoefficientShearEqualityParameterCover
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameterCover
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroRetainedDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing

/-!
# Full start-zero adjacent component restrictions

Both complete affine charts recover each original cyclic component, including scale one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)
    (Nat.zero_lt_succ (2 * s + 2)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueStrictZeroGluedCoconeDesc
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs (Nat.le_of_lt hk) h3 h4 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

/-- The entire first adjacent conic chart recovers its original cyclic position. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_first_left (j : Fin s) :
    ProjectiveLine.left Q ≫ B j 0 ≫ M =
      ProjectiveLine.right Q ≫ F ⟨j.val + 1, by omega⟩ := by
  by_cases hj0 : j.val = 0
  · have hspos : 0 < s := by omega
    have hj : j = ⟨0, hspos⟩ := Fin.ext hj0
    subst j
    rw [coefficientShearResidueAdjacentComponent_scaleOne_first_left_assoc
      (hjzero := by simp)]
    simp only [coefficientConicFirstParameter,
      coefficientShearRetainedTensorChart, Category.assoc]
    erw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
      coefficientShearResidueStrictZeroAtlasCoconeMap_first]
    simpa only [coefficientShearRetainedScaleOneTensorIso, Fin.val_castSucc,
      Category.assoc] using coefficientShearResidueStrictZeroFirstCoconeDesc_first
        hπ hm data s hs hk h3 h4 h6 hc C
  · rw [coefficientShearResidueAdjacentComponent_positive_first_left_assoc
      (hjpos := by omega)]
    simp only [coefficientConicFirstParameter, coefficientShearRetainedConic,
      coefficientShearRetainedFiber, Category.assoc]
    rw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart]
    rw [coefficientShearResidueStrictZeroAtlasCoconeMap_positive_index
      hπ hm data s hs hk h3 h4 h6 hc C j.castSucc (by dsimp; omega)]
    simpa only [coefficientShearRetainedEquationIso, Fin.val_castSucc, Category.assoc] using
      coefficientShearResidueStrictZeroRetainedDesc_first_conic
        hπ hm data s hs hk h3 h4 h6 hc j.castSucc (by dsimp; omega) F w

/-- The entire second adjacent conic chart recovers its original cyclic position. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_second_left (j : Fin s) :
    ProjectiveLine.left Q ≫ B j 1 ≫ M =
      ProjectiveLine.left Q ≫ F ⟨2 * s + 2 - j.val, by omega⟩ := by
  by_cases hj0 : j.val = 0
  · have hspos : 0 < s := by omega
    have hj : j = ⟨0, hspos⟩ := Fin.ext hj0
    subst j
    rw [coefficientShearResidueAdjacentComponent_scaleOne_second_left_assoc
      (hjzero := by simp)]
    simp only [coefficientConicSecondParameter,
      coefficientShearRetainedTensorChart, Category.assoc]
    erw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart,
      coefficientShearResidueStrictZeroAtlasCoconeMap_first]
    simpa only [coefficientShearRetainedScaleOneTensorIso, Fin.val_castSucc,
      Category.assoc, Nat.sub_zero] using coefficientShearResidueStrictZeroFirstCoconeDesc_second
        hπ hm data s hs hk h3 h4 h6 hc C
  · rw [coefficientShearResidueAdjacentComponent_positive_second_left_assoc
      (hjpos := by omega)]
    simp only [coefficientConicSecondParameter, coefficientShearRetainedConic,
      coefficientShearRetainedFiber, Category.assoc]
    rw [coefficientShearResidueStrictZeroGluedCoconeDesc_chart]
    rw [coefficientShearResidueStrictZeroAtlasCoconeMap_positive_index
      hπ hm data s hs hk h3 h4 h6 hc C j.castSucc (by dsimp; omega)]
    simpa only [coefficientShearRetainedEquationIso, Fin.val_castSucc, Category.assoc] using
      coefficientShearResidueStrictZeroRetainedDesc_second_conic
        hπ hm data s hs hk h3 h4 h6 hc j.castSucc (by dsimp; omega) F w

/-- The complete first adjacent right chart retains its actual signed parameter. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_first_right (j : Fin s) :
    ProjectiveLine.right Q ≫ B j 0 ≫ M =
      ProjectiveLine.left Q ≫ F ⟨j.val + 1, by omega⟩ := by
  rw [coefficientShearResidueAdjacentComponent_full_first_right_assoc,
    coefficientShearResidueStrictZeroGluedCoconeDesc_first_line
      hπ hm data s hs hk h3 h4 h6 hc C j.succ (by simp),
    ← Category.assoc, ← ProjectiveLine.chartScaling_mul]
  simp only [inv_mul_cancel, ProjectiveLine.chartScaling_one, Category.id_comp, Fin.val_succ]

/-- The complete second adjacent right chart retains its actual signed parameter. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_second_right (j : Fin s) :
    ProjectiveLine.right Q ≫ B j 1 ≫ M =
      ProjectiveLine.right Q ≫ F ⟨2 * s + 2 - j.val, by omega⟩ := by
  rw [coefficientShearResidueAdjacentComponent_full_second_right_assoc,
    coefficientShearResidueStrictZeroGluedCoconeDesc_second_line
      hπ hm data s hs hk h3 h4 h6 hc C j.succ (by simp),
    ← Category.assoc, ← ProjectiveLine.chartScaling_mul]
  simp only [inv_mul_cancel, ProjectiveLine.chartScaling_one, Category.id_comp]
  congr 2
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

/-- The entire first adjacent component recovers its original cyclic cocone map. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_adjacent_first (j : Fin s) :
    B j 0 ≫ M = ρ ≫ F ⟨j.val + 1, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ B j 0 ≫ M =
      ProjectiveLine.left Q ≫ ρ ≫ F ⟨j.val + 1, by omega⟩
    rw [ProjectiveLine.left_endpointReversal_assoc]
    exact coefficientShearResidueStrictZeroGluedCoconeDesc_first_left ..
  · change ProjectiveLine.right Q ≫ B j 0 ≫ M =
      ProjectiveLine.right Q ≫ ρ ≫ F ⟨j.val + 1, by omega⟩
    rw [ProjectiveLine.right_endpointReversal_assoc]
    exact coefficientShearResidueStrictZeroGluedCoconeDesc_first_right ..

/-- The entire second adjacent component recovers its original cyclic cocone map. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_adjacent_second (j : Fin s) :
    B j 1 ≫ M = F ⟨2 * s + 2 - j.val, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ B j 1 ≫ M = _
    exact coefficientShearResidueStrictZeroGluedCoconeDesc_second_left ..
  · change ProjectiveLine.right Q ≫ B j 1 ≫ M = _
    exact coefficientShearResidueStrictZeroGluedCoconeDesc_second_right ..

end FLT.Mazur.WeierstrassDividedDepth
