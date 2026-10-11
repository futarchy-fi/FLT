/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCyclicSmoothParameter
public import FLT.Mazur.WeierstrassSmoothHorizontalFactorOrder

/-!
# The actual cyclic smooth parameter on the horizontal residue product

The independent smooth factor maps to the original cyclic torus. Its unit
is exactly the inverse tangent unit occurring in the retained first-line action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
open WeierstrassDividedDepth
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "C" => SmoothHorizontalResidueRing D
local notation "τ" => smoothHorizontalTangentUnit D
local notation "j" => smoothHorizontalResidueParameter D

/-- The cyclic coordinate on the actual independent smooth factor. -/
def smoothHorizontalCyclicParameter : L →ₐ[K] C :=
  (j).comp (smoothYParameterCyclicAlgebra D)

/-- The actual cyclic torus point has the inverse tangent unit. -/
theorem smoothHorizontalCyclicParameter_unit :
    LaurentUnitPoints.pointUnit (smoothHorizontalCyclicParameter D) = τ⁻¹ := by
  apply inv_injective
  rw [inv_inv]
  apply Units.ext
  change j (smoothYParameterCyclicAlgebra D (LaurentPolynomial.T (-1))) = (τ : C)
  rw [smoothYParameterCyclicAlgebra_T, neg_neg, smoothHorizontalTangentUnit_val]

/-- The inverse-character evaluation is the entire actual cyclic parameter map. -/
theorem smoothHorizontalCyclicParameter_evaluation :
    smoothHorizontalLaurentEvaluation D τ⁻¹ = smoothHorizontalCyclicParameter D := by
  have h := LaurentUnitPoints.evalUnit_pointUnit (smoothHorizontalCyclicParameter D)
  rw [smoothHorizontalCyclicParameter_unit] at h
  exact h

/-- Spectrum retains the original smooth factor projection and its cyclic orientation. -/
theorem smoothHorizontalCyclicParameter_spec :
    Spec.map (CommRingCat.ofHom (smoothHorizontalCyclicParameter D).toRingHom) =
      Spec.map (CommRingCat.ofHom (j).toRingHom) ≫ smoothYParameterCyclicMap D := by
  rw [← smoothYParameterCyclicAlgebra_spec, ← Spec.map_comp]
  rfl

/-- Interchange places the actual cyclic parameter in the first tensor factor. -/
theorem smoothHorizontalCyclicParameter_interchange :
    (smoothHorizontalResidueInterchange D).toAlgHom.comp (smoothHorizontalCyclicParameter D) =
      (Algebra.TensorProduct.includeLeft : P →ₐ[K] P ⊗[K] L).comp
        (smoothYParameterCyclicAlgebra D) := by
  apply AlgHom.ext
  intro f
  exact smoothHorizontalResidueInterchange_parameter D (smoothYParameterCyclicAlgebra D f)

variable [IsDomain R] {start : ℕ} (s : ℕ) (hk : 2 * (start + s + 1) ≤ depth)
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk

/-- The inverse tangent character is the original smooth point under the actual group iso. -/
theorem smoothHorizontalCyclicParameter_original :
    Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D τ⁻¹).toRingHom) ≫
        (v).hom.hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom (j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L P)) ≫
          (infinityResidueSmoothIso D hd).hom := by
  rw [smoothHorizontalCyclicParameter_evaluation, smoothHorizontalCyclicParameter_spec,
    Category.assoc, smoothYParameterCyclicMap_original]

end FLT.Mazur.WeierstrassIntegralChart
