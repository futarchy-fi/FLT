/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveTransportedTensorInput
public import FLT.Mazur.WeierstrassSuccessiveZeroConicMap
public import FLT.Mazur.WeierstrassSmoothHorizontalLaurentEvaluation

/-!
# The scale-one inputs are the independently constructed signed conic points

Scalar extension of each actual integral residue input factors through its
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
local notation "J" => smoothHorizontalResidueConic D

/-- The first integral input is the actual positive scale-one conic puncture. -/
theorem smoothSuccessiveFirstTransportedTensorInput_zeroConic :
    smoothSuccessiveFirstTransportedTensorInput d hπ D hk =
      (J).comp ((P₁).comp F) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  simp only [smoothSuccessiveFirstTransportedTensorInput, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  change smoothSuccessiveFirstResidueInput d hπ D (Nat.zero_lt_succ k) hk
    (WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 i) =
      J
        (P₁ (F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)))
  fin_cases i
  · conv_rhs => erw [zeroResidueConicMap_t D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveFirstResidueInput_t d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedFirst, conicEvaluation_t]
    rfl
  · conv_rhs => erw [zeroResidueConicMap_v D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveFirstResidueInput_v d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedFirst, conicEvaluation_v, map_zero]
  · conv_rhs => erw [zeroResidueConicMap_u D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveFirstResidueInput_u d hπ D (Nat.zero_lt_succ k) hk]
    change _ = J (P₁ 0)
    rw [map_zero, map_zero]

/-- The opposite integral input retains the actual negative scale-one conic puncture. -/
theorem smoothSuccessiveSecondTransportedTensorInput_zeroConic :
    smoothSuccessiveSecondTransportedTensorInput d hπ D hk =
      (J).comp ((P₂).comp F) := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  simp only [smoothSuccessiveSecondTransportedTensorInput, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  change smoothSuccessiveSecondResidueInput d hπ D (Nat.zero_lt_succ k) hk
    (WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 i) =
      J
        (P₂ (F (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)))
  fin_cases i
  · conv_rhs => erw [zeroResidueConicMap_t D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveSecondResidueInput_t d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedSecond, conicEvaluation_t]
    rfl
  · conv_rhs => erw [zeroResidueConicMap_v D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveSecondResidueInput_v d hπ D (Nat.zero_lt_succ k) hk]
    erw [conicPuncturedSecond, conicEvaluation_v, map_neg]
    change -algebraMap R C W.a₁ = -(J (algebraMap K _ (residue R W.a₁)))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R K C, ResidueField.algebraMap_eq]
  · conv_rhs => erw [zeroResidueConicMap_u D hk0 (Nat.le_of_lt hk) d]
    erw [smoothSuccessiveSecondResidueInput_u d hπ D (Nat.zero_lt_succ k) hk]
    change _ = J (P₂ 0)
    rw [map_zero, map_zero]

end FLT.Mazur.WeierstrassIntegralChart
