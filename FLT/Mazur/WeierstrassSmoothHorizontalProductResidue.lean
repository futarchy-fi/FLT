/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalProductSource
public import FLT.Mazur.WeierstrassSmoothYAffineResidue
public import FLT.Mazur.WeierstrassHorizontalConicPunctureResidue

/-!
# The actual conic puncture times the named smooth parameter

Both branch residue maps start on the integral product source. They evaluate
the retained horizontal fraction chart on its actual conic puncture and the
smooth input on its named Laurent parameter, with independent coordinates.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D

/-- The two independent residue parameters on the conic and smooth factors. -/
def SmoothHorizontalResidueRing := L ⊗[K] P

instance smoothHorizontalResidueCommRing : CommRing (SmoothHorizontalResidueRing D) :=
  inferInstanceAs (CommRing (L ⊗[K] P))

instance smoothHorizontalResidueAlgebra : Algebra K (SmoothHorizontalResidueRing D) :=
  inferInstanceAs (Algebra K (L ⊗[K] P))

instance smoothHorizontalResidueAlgebraBase : Algebra R (SmoothHorizontalResidueRing D) :=
  inferInstanceAs (Algebra R (L ⊗[K] P))

instance smoothHorizontalResidueTower : IsScalarTower R K (SmoothHorizontalResidueRing D) :=
  inferInstanceAs (IsScalarTower R K (L ⊗[K] P))

local notation "C" => SmoothHorizontalResidueRing D
local notation "S" => SmoothHorizontalProductRing W (π ^ k)
local notation "H" => HorizontalSourceRing W (π ^ k)

/-- The conic parameter inclusion on the residue product. -/
def smoothHorizontalResidueConic : L →ₐ[K] C := Algebra.TensorProduct.includeLeft

/-- The named smooth parameter inclusion on the residue product. -/
def smoothHorizontalResidueParameter : P →ₐ[K] C := Algebra.TensorProduct.includeRight

open WeierstrassModificationX
local notation "f₁" => horizontalConicFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
local notation "f₂" => horizontalConicSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
local notation "g" => smoothYAffineResidue D (by omega)
local notation "l" => AlgHom.restrictScalars R (smoothHorizontalResidueConic D)
local notation "r" => AlgHom.restrictScalars R (smoothHorizontalResidueParameter D)

/-- The first actual branch on the integral common product source. -/
def smoothHorizontalFirstResidue : S →ₐ[R] C :=
  Algebra.TensorProduct.lift ((l).comp (show H →ₐ[R] L from f₁))
    ((r).comp g) (fun _ _ => Commute.all _ _)

/-- The opposite actual branch on the same integral common product source. -/
def smoothHorizontalSecondResidue : S →ₐ[R] C :=
  Algebra.TensorProduct.lift ((l).comp (show H →ₐ[R] L from f₂))
    ((r).comp g) (fun _ _ => Commute.all _ _)

/-- The first product residue retains every original horizontal fraction function. -/
theorem smoothHorizontalFirstResidue_input (q : HorizontalSourceRing W (π ^ k)) :
    smoothHorizontalFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (smoothHorizontalInput W (π ^ k) q) = smoothHorizontalResidueConic D (f₁ q) := by
  change Algebra.TensorProduct.lift _ _ _ (q ⊗ₜ[R] 1) = _
  simp only [Algebra.TensorProduct.lift_tmul, map_one, mul_one, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]
  rfl

/-- The opposite product residue retains every original horizontal fraction function. -/
theorem smoothHorizontalSecondResidue_input (q : HorizontalSourceRing W (π ^ k)) :
    smoothHorizontalSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (smoothHorizontalInput W (π ^ k) q) = smoothHorizontalResidueConic D (f₂ q) := by
  change Algebra.TensorProduct.lift _ _ _ (q ⊗ₜ[R] 1) = _
  simp only [Algebra.TensorProduct.lift_tmul, map_one, mul_one, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]
  rfl

/-- The first branch preserves the entire independent smooth parameter factor. -/
theorem smoothHorizontalFirstResidue_parameter (q : SmoothYAffineRing W) :
    smoothHorizontalFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (smoothHorizontalParameter W (π ^ k) q) = smoothHorizontalResidueParameter D (g q) := by
  change Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ[R] q) = _
  simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]

/-- The first residue map kills the original base maximal ideal. -/
theorem smoothHorizontalFirstResidue_maximal :
    (maximalIdeal R).map (algebraMap R S) ≤
      RingHom.ker (smoothHorizontalFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  change smoothHorizontalFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
    (algebraMap R S q) = 0
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R K C,
    ResidueField.algebraMap_eq, (residue_eq_zero_iff q).mpr hq, map_zero]

/-- The second branch preserves the entire independent smooth parameter factor. -/
theorem smoothHorizontalSecondResidue_parameter (q : SmoothYAffineRing W) :
    smoothHorizontalSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (smoothHorizontalParameter W (π ^ k) q) = smoothHorizontalResidueParameter D (g q) := by
  change Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ[R] q) = _
  simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply]

/-- The second residue map kills the original base maximal ideal. -/
theorem smoothHorizontalSecondResidue_maximal :
    (maximalIdeal R).map (algebraMap R S) ≤
      RingHom.ker (smoothHorizontalSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  change smoothHorizontalSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
    (algebraMap R S q) = 0
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R K C,
    ResidueField.algebraMap_eq, (residue_eq_zero_iff q).mpr hq, map_zero]

/-- The first residue input has zero original horizontal denominator. -/
theorem smoothHorizontalFirstResidue_denominator :
    smoothHorizontalFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (smoothHorizontalInput W (π ^ k) (BlowupFractionChart.denominator
        (modificationChartCenter W (π ^ k) 2) (coord W 2 0))) = 0 := by
  rw [smoothHorizontalFirstResidue_input]
  exact (congrArg (smoothHorizontalResidueConic D)
    (horizontalConicFirstResidue_denominator D k hk0 hk hπ b3 b4 b6 h3 h4 h6)).trans
      (map_zero _)

/-- The second residue input has zero original horizontal denominator. -/
theorem smoothHorizontalSecondResidue_denominator :
    smoothHorizontalSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (smoothHorizontalInput W (π ^ k) (BlowupFractionChart.denominator
        (modificationChartCenter W (π ^ k) 2) (coord W 2 0))) = 0 := by
  rw [smoothHorizontalSecondResidue_input]
  exact (congrArg (smoothHorizontalResidueConic D)
    (horizontalConicSecondResidue_denominator D k hk0 hk hπ b3 b4 b6 h3 h4 h6)).trans
      (map_zero _)

end FLT.Mazur.WeierstrassIntegralChart
