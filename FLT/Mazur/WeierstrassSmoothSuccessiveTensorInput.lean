/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalTensorInput
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleComponents
public import FLT.Mazur.WeierstrassDividedFiniteLineReciprocals

/-!
# Independent horizontal residue inputs on the successive equation chart

These algebra maps retain the same independently constructed smooth and
Laurent parameters used on the initial chart. They evaluate the actual
successive tensor algebra through its original ordered conic punctures.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hk0 : 0 < k)
  (hk : 2 * (k + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => ScalarExtension W (π ^ k) π d.b3 d.b4 d.b6 K
local notation "a" => residue R W.a₁
local notation "c" => residue R d.b6
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (k + 1) hk d.b6 d.factor6)
local notation "F" => residueSuccessiveConicMap D k hk0 (Nat.le_of_lt hk)
  d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "P₁" => conicPuncturedFirst (W.map (residue R)) c hc
local notation "P₂" => conicPuncturedSecond (W.map (residue R)) c hc

/-- The independent first conic input in the actual successive tensor equation algebra. -/
def smoothSuccessiveFirstTensorInput : A →ₐ[K] C :=
  (smoothHorizontalResidueConic D).comp ((P₁).comp F)

/-- The independent opposite conic input with its original negative tangent scale. -/
def smoothSuccessiveSecondTensorInput : A →ₐ[K] C :=
  (smoothHorizontalResidueConic D).comp ((P₂).comp F)

/-- The first algebra input factors through the actual successive conic immersion. -/
theorem smoothSuccessiveFirstTensorInput_spec :
    Spec.map (CommRingCat.ofHom (smoothSuccessiveFirstTensorInput D d hk0 hk).toRingHom) =
      Spec.map (CommRingCat.ofHom (smoothHorizontalResidueConic D).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (P₁).toRingHom) ≫
          residueSuccessiveConicImmersion D k hk0 (Nat.le_of_lt hk)
            d.b3 d.b4 d.b6 d.factor3 d.factor4 := by
  rw [smoothSuccessiveFirstTensorInput, WeierstrassDividedDepth.lineSpec_comp,
    WeierstrassDividedDepth.lineSpec_comp, residueSuccessiveConicMap,
    WeierstrassDividedDepth.lineSpec_comp]
  rfl

/-- The opposite algebra input uses the same original conic immersion. -/
theorem smoothSuccessiveSecondTensorInput_spec :
    Spec.map (CommRingCat.ofHom (smoothSuccessiveSecondTensorInput D d hk0 hk).toRingHom) =
      Spec.map (CommRingCat.ofHom (smoothHorizontalResidueConic D).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (P₂).toRingHom) ≫
          residueSuccessiveConicImmersion D k hk0 (Nat.le_of_lt hk)
            d.b3 d.b4 d.b6 d.factor3 d.factor4 := by
  rw [smoothSuccessiveSecondTensorInput, WeierstrassDividedDepth.lineSpec_comp,
    WeierstrassDividedDepth.lineSpec_comp, residueSuccessiveConicMap,
    WeierstrassDividedDepth.lineSpec_comp]
  rfl

/-- First incidence retains the independent conic parameter with positive tangent scale. -/
theorem smoothSuccessiveFirstTensorInput_t :
    smoothSuccessiveFirstTensorInput D d hk0 hk
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 0) =
        smoothHorizontalResidueConic D (LaurentPolynomial.C a * LaurentPolynomial.T 1) := by
  rw [smoothSuccessiveFirstTensorInput, AlgHom.comp_apply, AlgHom.comp_apply]
  erw [residueSuccessiveConicMap_coord]
  change smoothHorizontalResidueConic D (P₁ (conicT a c)) = _
  erw [conicPuncturedFirst, conicEvaluation_t]
  rw [WeierstrassCurve.map_a₁]

/-- The first input lies on the zero-slope branch. -/
theorem smoothSuccessiveFirstTensorInput_v :
    smoothSuccessiveFirstTensorInput D d hk0 hk
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 1) = 0 := by
  rw [smoothSuccessiveFirstTensorInput, AlgHom.comp_apply, AlgHom.comp_apply]
  erw [residueSuccessiveConicMap_coord]
  change smoothHorizontalResidueConic D (P₁ (conicV a c)) = _
  erw [conicPuncturedFirst, conicEvaluation_v, map_zero]

/-- The retained horizontal coordinate vanishes on the first conic input. -/
theorem smoothSuccessiveFirstTensorInput_u :
    smoothSuccessiveFirstTensorInput D d hk0 hk
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 2) = 0 := by
  rw [smoothSuccessiveFirstTensorInput, AlgHom.comp_apply, AlgHom.comp_apply]
  erw [residueSuccessiveConicMap_coord]
  change smoothHorizontalResidueConic D (P₁ 0) = _
  rw [map_zero, map_zero]

/-- Opposite incidence retains the independent conic parameter with negative tangent scale. -/
theorem smoothSuccessiveSecondTensorInput_t :
    smoothSuccessiveSecondTensorInput D d hk0 hk
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 0) =
        smoothHorizontalResidueConic D (-LaurentPolynomial.C a * LaurentPolynomial.T 1) := by
  rw [smoothSuccessiveSecondTensorInput, AlgHom.comp_apply, AlgHom.comp_apply]
  erw [residueSuccessiveConicMap_coord]
  change smoothHorizontalResidueConic D (P₂ (conicT a c)) = _
  erw [conicPuncturedSecond, conicEvaluation_t]
  rw [WeierstrassCurve.map_a₁]

/-- The opposite input has minus the original tangent coefficient as its slope. -/
theorem smoothSuccessiveSecondTensorInput_v :
    smoothSuccessiveSecondTensorInput D d hk0 hk
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 1) = -algebraMap K C a := by
  rw [smoothSuccessiveSecondTensorInput, AlgHom.comp_apply, AlgHom.comp_apply]
  erw [residueSuccessiveConicMap_coord]
  change smoothHorizontalResidueConic D (P₂ (conicV a c)) = _
  erw [conicPuncturedSecond, conicEvaluation_v, map_neg]
  exact congrArg Neg.neg ((smoothHorizontalResidueConic D).commutes a)

/-- The retained horizontal coordinate also vanishes on the opposite conic input. -/
theorem smoothSuccessiveSecondTensorInput_u :
    smoothSuccessiveSecondTensorInput D d hk0 hk
      (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K 2) = 0 := by
  rw [smoothSuccessiveSecondTensorInput, AlgHom.comp_apply, AlgHom.comp_apply]
  erw [residueSuccessiveConicMap_coord]
  change smoothHorizontalResidueConic D (P₂ 0) = _
  rw [map_zero, map_zero]

end FLT.Mazur.WeierstrassIntegralChart
