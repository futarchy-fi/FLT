/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthResidueEquation
public import FLT.Mazur.WeierstrassChartBaseChange

/-!
# Laurent normalization of the entire original infinity tensor algebra

Positive split depth identifies the actual tensor chart with the Laurent
algebra. The original projective X, Y and Z coordinates are retained, and
the Laurent generator is the ordered tangent factor 1+a₁X/Y.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
open WeierstrassDilatation
local notation "K" => ResidueField R
local notation "a" => residueTangentUnit D

/-- Named original tensor coordinates keep the chart algebra sealed. -/
def infinityTensorCoord (i : Fin 3) : ChartScalarExtension K W 1 :=
  (1 : K) ⊗ₜ[R] coord W 1 i

/-- The complete tensor infinity chart, with its actual residue coefficients. -/
def infinityResidueEquiv : ChartScalarExtension K W 1 ≃ₐ[K] K[T;T⁻¹] :=
  (chartBaseChangeEquiv K W 1).trans
    ((equationChartEquiv (splitDepth_residue_equation D hdepth) 1).trans
      (splitNodalChartLaurentEquiv a))

/-- Every original normalized coordinate has its explicit Laurent value. -/
theorem infinityResidueEquiv_coord (i : Fin 3) :
    infinityResidueEquiv D hdepth ((1 : K) ⊗ₜ[R] coord W 1 i) =
      ![splitNodalLaurentX a, 1, splitNodalLaurentZ a] i := by
  simp only [infinityResidueEquiv, AlgEquiv.trans_apply, chartBaseChangeEquiv_coord,
    equationChartEquiv_coord]
  exact splitNodalChartToLaurent_coord a i

/-- The original tangent factor maps to the positive Laurent generator. -/
theorem infinityResidueEquiv_tangent :
    infinityResidueEquiv D hdepth
      (1 + algebraMap K (ChartScalarExtension K W 1) (residue R W.a₁) *
        (infinityTensorCoord (W := W) 0)) = LaurentPolynomial.T 1 := by
  rw [map_add, map_one, map_mul, AlgEquiv.commutes,
    infinityTensorCoord, infinityResidueEquiv_coord]
  rw [← residueTangentUnit_val D]
  exact splitNodalLaurent_tangent a

/-- The inverse normalization recovers the original ordered tangent factor. -/
theorem infinityResidueEquiv_symm_tangent :
    (infinityResidueEquiv D hdepth).symm (LaurentPolynomial.T 1) =
      1 + algebraMap K (ChartScalarExtension K W 1) (residue R W.a₁) *
        (infinityTensorCoord (W := W) 0) :=
  (infinityResidueEquiv D hdepth).symm_apply_eq.mpr
    (infinityResidueEquiv_tangent D hdepth).symm

end FLT.Mazur.WeierstrassIntegralChart
