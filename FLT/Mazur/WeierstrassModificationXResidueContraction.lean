/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueFiber
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# Original contraction functions in the tensor residue fiber

The original x and y functions are transported through the existing tensor
normal-form equivalence. The formulas retain the images of the actual t and
v tensors and the full middle-depth coefficient. Identifying those images
with the named normal-form generators is a separate transport calculation.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section General

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (f : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h2 : algebraMap R S W.a₂ = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)

include h2 h3 h4 in
/-- The recovered horizontal function keeps its quadratic depth coefficient. -/
theorem map_x_of_linear_zero : f (x W s b3 b4 b6) =
    f (v W s b3 b4 b6) * (f (v W s b3 b4 b6) + algebraMap R S W.a₁) -
      algebraMap R S b6 * f (t W s b3 b4 b6) ^ 2 := by
  simp only [x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes,
    h2, h3, h4, zero_mul, zero_add, add_zero]
  ring

include h2 h3 h4 in
/-- The recovered vertical function retains the original tangent slope. -/
theorem map_y_of_linear_zero : f (y W s b3 b4 b6) =
    (f (v W s b3 b4 b6) * (f (v W s b3 b4 b6) + algebraMap R S W.a₁) -
      algebraMap R S b6 * f (t W s b3 b4 b6) ^ 2) * f (v W s b3 b4 b6) := by
  rw [y, map_mul, map_x_of_linear_zero W s b3 b4 b6 f h2 h3 h4]

end General

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)

local notation "K" => ResidueField R
local notation "F" => FiberCoordinate (residue R W.a₁) (residue R b6)

/-- The old chart map into the existing normal form of its actual tensor residue fiber. -/
def residueNormalMap : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] F :=
  ((residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The chart map is exactly the existing equivalence applied to the original pure tensor. -/
theorem residueNormalMap_apply (z : Coordinate W (π ^ k) b3 b4 b6) :
    residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 z =
      residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 ((1 : K) ⊗ₜ[R] z) := rfl

omit [IsDomain R] in
/-- Every coefficient in the original maximal ideal vanishes in the actual normal form. -/
theorem residueNormal_coefficient_zero (r : R) (hr : r ∈ maximalIdeal R) :
    algebraMap R F r = 0 := by
  rw [IsScalarTower.algebraMap_apply R K F, ResidueField.algebraMap_eq,
    (residue_eq_zero_iff r).mpr hr, map_zero]

/-- The actual tensor comparison transports x to the full quadratic expression. -/
theorem residueNormalMap_x :
    let f := residueNormalMap D k hk0 hk b3 b4 b6 h3 h4
    f (x W (π ^ k) b3 b4 b6) =
      f (v W (π ^ k) b3 b4 b6) *
        (f (v W (π ^ k) b3 b4 b6) + algebraMap R F W.a₁) -
          algebraMap R F b6 * f (t W (π ^ k) b3 b4 b6) ^ 2 := by
  obtain ⟨hb3, hb4⟩ := WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4
  exact map_x_of_linear_zero W _ _ _ _ _
    (residueNormal_coefficient_zero b6 W.a₂ D.a₂_mem)
    (residueNormal_coefficient_zero b6 b3 hb3)
    (residueNormal_coefficient_zero b6 b4 hb4)

/-- The transported original y is the transported x times the original tensor slope. -/
theorem residueNormalMap_y :
    let f := residueNormalMap D k hk0 hk b3 b4 b6 h3 h4
    f (y W (π ^ k) b3 b4 b6) =
      f (x W (π ^ k) b3 b4 b6) * f (v W (π ^ k) b3 b4 b6) := by
  exact map_mul _ _ _

variable (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

/-- The original cubic coordinate map, followed by the actual tensor normal-form comparison. -/
def residueOriginalCoordinateMap : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] F :=
  (residueNormalMap D k hk0 hk b3 b4 b6 h3 h4).comp
    (fromOriginal W (π ^ k) b3 b4 b6 h3 h4 h6)

/-- The original cubic's x coordinate is the transported horizontal contraction function. -/
@[simp] theorem residueOriginalCoordinateMap_x :
    residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6
      (WeierstrassIntegralChart.coord W 2 0) =
        residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 (x W (π ^ k) b3 b4 b6) := by
  simp only [residueOriginalCoordinateMap, AlgHom.comp_apply, fromOriginal_x]

/-- The original cubic's y coordinate is the transported vertical contraction function. -/
@[simp] theorem residueOriginalCoordinateMap_y :
    residueOriginalCoordinateMap D k hk0 hk b3 b4 b6 h3 h4 h6
      (WeierstrassIntegralChart.coord W 2 1) =
        residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 (y W (π ^ k) b3 b4 b6) := by
  simp only [residueOriginalCoordinateMap, AlgHom.comp_apply, fromOriginal_y]

end FLT.Mazur.WeierstrassModificationX
