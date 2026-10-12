/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveTensorOutput
public import FLT.Mazur.WeierstrassSuccessiveZeroConicMap
public import FLT.Mazur.WeierstrassSmoothHorizontalLaurentEvaluation

/-!
# The scale-one tensor outputs are the original signed conic actions

Scalar extension of each actual integral residue output factors through its
original conic puncture. All three coordinates determine the complete tensor map.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
  (D : SplitNodeDepth W π depth) (hk0 : k = 0) (hk : 2 * (k + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ k) π d.b3 d.b4 d.b6
local notation "B" => ScalarExtension W (π ^ k) π d.b3 d.b4 d.b6 K
local notation "a" => residue R W.a₁
local notation "c" => residue R d.b6
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (k + 1) hk d.b6 d.factor6)
local notation "F" => zeroResidueConicMap D hk0 (Nat.le_of_lt hk) d
local notation "P₁" => conicPuncturedFirst (W.map (residue R)) c hc
local notation "P₂" => conicPuncturedSecond (W.map (residue R)) c hc
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D

/-- Every first output function is the positive-character Laurent conic substitution. -/
theorem smoothSuccessiveFirstTensorOutput_zeroConic :
    smoothSuccessiveFirstTensorOutput d hπ D hk =
      (smoothHorizontalLaurentEvaluation D (τ * z)).comp ((P₁).comp F) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  simp only [smoothSuccessiveFirstTensorOutput, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  change smoothSuccessiveFirstResidueOutput d hπ D (Nat.zero_lt_succ k) hk
    (WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 i) =
      smoothHorizontalLaurentEvaluation D (τ * z)
        (P₁ (F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)))
  fin_cases i
  · conv_rhs => erw [zeroResidueConicMap_t D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveFirstResidueOutput_t d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedFirst, conicEvaluation_t]
    rw [WeierstrassCurve.map_a₁, smoothHorizontalLaurentEvaluation_first]
  · conv_rhs => erw [zeroResidueConicMap_v D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveFirstResidueOutput_v d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedFirst, conicEvaluation_v, map_zero]
  · conv_rhs => erw [zeroResidueConicMap_u D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveFirstResidueOutput_u d hπ D (Nat.zero_lt_succ k) hk]
    change _ = smoothHorizontalLaurentEvaluation D (τ * z) (P₁ 0)
    rw [map_zero, map_zero]

/-- Every opposite output function keeps the inverse character and negative conic scale. -/
theorem smoothSuccessiveSecondTensorOutput_zeroConic :
    smoothSuccessiveSecondTensorOutput d hπ D hk =
      (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).comp ((P₂).comp F) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  simp only [smoothSuccessiveSecondTensorOutput, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  change smoothSuccessiveSecondResidueOutput d hπ D (Nat.zero_lt_succ k) hk
    (WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 i) =
      smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)
        (P₂ (F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)))
  fin_cases i
  · conv_rhs => erw [zeroResidueConicMap_t D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveSecondResidueOutput_t d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedSecond, conicEvaluation_t]
    rw [WeierstrassCurve.map_a₁, smoothHorizontalLaurentEvaluation_second]
  · conv_rhs => erw [zeroResidueConicMap_v D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveSecondResidueOutput_v d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedSecond, conicEvaluation_v, map_neg]
    rw [WeierstrassCurve.map_a₁, smoothHorizontalLaurentEvaluation_C,
      IsScalarTower.algebraMap_apply R K C, ResidueField.algebraMap_eq]
  · conv_rhs => erw [zeroResidueConicMap_u D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveSecondResidueOutput_u d hπ D (Nat.zero_lt_succ k) hk]
    change _ = smoothHorizontalLaurentEvaluation D (τ⁻¹ * z) (P₂ 0)
    rw [map_zero, map_zero]

end FLT.Mazur.WeierstrassIntegralChart
