/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedProductSource
public import FLT.Mazur.WeierstrassSmoothHorizontalResidueCoordinates
public import FLT.Mazur.WeierstrassDilatationLaurentPointCharacters

/-!
# The terminal Laurent chart times the independent smooth parameter

The residue map is defined on the integral divided product. It retains the
original divided coordinates and the named smooth parameter independently.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k ≤ depth)
  (hp : 2 * k = depth)
local notation "𝕂" => ResidueField R
local notation "L" => 𝕂[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "C" => SmoothHorizontalResidueRing D
local notation "H" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "S" => SmoothDividedProductRing W (π ^ k) d.b3 d.b4 d.b6
local notation "e" => residueLaurentEquiv D k hk0 hk d.b3 d.b4 d.b6
  d.factor3 d.factor4 d.factor6 hp
local notation "j" => smoothHorizontalResidueParameter D
local notation "l" => smoothHorizontalResidueConic D

/-- The actual integral divided chart evaluated on its terminal Laurent fiber. -/
def smoothDividedTerminalResidue : H →ₐ[R] L :=
  ((e).toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

/-- The original divided vertical coordinate is the first independent Laurent variable. -/
theorem smoothDividedTerminalResidue_y :
    smoothDividedTerminalResidue D d hk0 hk hp
      (WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6) = LaurentPolynomial.T 1 :=
  residueLaurentEquiv_y D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 hp

/-- The genuine terminal by smooth residue specialization of the integral product. -/
def smoothDividedProductResidue : S →ₐ[R] C :=
  Algebra.TensorProduct.lift
    (((l).restrictScalars R).comp (smoothDividedTerminalResidue D d hk0 hk hp))
    (((j).restrictScalars R).comp (smoothYAffineResidue D (by omega)))
    (fun _ _ => Commute.all _ _)

/-- The product residue preserves every original integral divided function. -/
theorem smoothDividedProductResidue_input (q : H) :
    smoothDividedProductResidue D d hk0 hk hp
      (smoothDividedInput W (π ^ k) d.b3 d.b4 d.b6 q) =
        l (smoothDividedTerminalResidue D d hk0 hk hp q) := by
  change Algebra.TensorProduct.lift _ _ _ (q ⊗ₜ[R] 1) = _
  simp only [Algebra.TensorProduct.lift_tmul, map_one, mul_one, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]

/-- It preserves the whole independent smooth parameter factor. -/
theorem smoothDividedProductResidue_parameter (q : SmoothYAffineRing W) :
    smoothDividedProductResidue D d hk0 hk hp
      (smoothDividedParameter W (π ^ k) d.b3 d.b4 d.b6 q) =
        j (smoothYAffineResidue D (by omega) q) := by
  change Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ[R] q) = _
  simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]

/-- The product residue annihilates the original maximal ideal. -/
theorem smoothDividedProductResidue_maximal :
    (maximalIdeal R).map (algebraMap R S) ≤
      RingHom.ker (smoothDividedProductResidue D d hk0 hk hp).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  change smoothDividedProductResidue D d hk0 hk hp (algebraMap R S q) = 0
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R 𝕂 C,
    ResidueField.algebraMap_eq, (residue_eq_zero_iff q).mpr hq, map_zero]

/-- The actual normalized smooth Y presentation retains its original named coordinates. -/
theorem smoothDividedProductResidue_Y (q : Coordinate W 1) :
    smoothDividedProductResidue D d hk0 hk hp
      (smoothDividedY W (π ^ k) d.b3 d.b4 d.b6 q) =
        j (algebraMap L P (smoothYParameterResidue D (by omega) q)) := by
  change smoothDividedProductResidue D d hk0 hk hp
    (smoothDividedParameter W (π ^ k) d.b3 d.b4 d.b6 (smoothYAffineY W q)) = _
  rw [smoothDividedProductResidue_parameter, smoothYAffineResidue_base]

/-- The genuine smooth input gives exactly the named positive tangent unit. -/
theorem smoothDividedProductResidue_tangent :
    (smoothHorizontalTangentUnit D : C) = 1 + algebraMap R C W.a₁ *
      smoothDividedProductResidue D d hk0 hk hp
        (smoothDividedY W (π ^ k) d.b3 d.b4 d.b6 (coord W 1 0)) := by
  rw [smoothHorizontalTangentUnit_val, smoothDividedProductResidue_Y,
    smoothYParameterResidue_coord]
  have h := congrArg (fun z : L => j (algebraMap L P z))
    (splitNodalLaurent_tangent (residueTangentUnit D))
  simp only [map_add, map_one, map_mul] at h
  rw [residueTangentUnit_val, smoothHorizontalResidue_coefficient] at h
  exact h.symm

end FLT.Mazur.WeierstrassIntegralChart
