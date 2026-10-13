/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearLineProjection
public import FLT.Mazur.WeierstrassModificationXMorphism

/-!
# The full original cubic coordinates on the sheared incidence line

The horizontal coordinate is the product of the two tangent factors; the
vertical coordinate retains the original root shift on the whole affine line.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "L" => originalShearInitialLineMap W s b3 b4 b6 S r hs h3 h4 hr

/-- The original horizontal coordinate keeps both tangent factors. -/
theorem originalShearInitialLineMap_x : L (x W s b3 b4 b6) = X * (X + C a) := by
  simp only [x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes,
    originalShearInitialLineMap_t, originalShearInitialLineMap_v, mul_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero]
  simp only [IsScalarTower.algebraMap_apply R S S[X], algebraMap_eq]
  rw [(rootShearCurve_coefficients r).1]
  change _ = X * (X + C (algebraMap R S W.a₁ + 2 * r))
  have h := congrArg (C : S →+* S[X]) hr
  simp only [map_sub, map_add, map_mul, map_pow, map_zero] at h
  simp only [map_add, map_mul, map_ofNat]
  linear_combination h

/-- The original vertical coordinate keeps the entire translated slope. -/
theorem originalShearInitialLineMap_y :
    L (y W s b3 b4 b6) = (X + C r) * (X * (X + C a)) := by
  rw [y, map_mul, originalShearInitialLineMap_x, originalShearInitialLineMap_v, mul_comm]

variable (g3 : W.a₃ = s * b3) (g4 : W.a₄ = s * b4) (g6 : W.a₆ = s ^ 2 * b6)

/-- Every original affine cubic function restricted to the complete incidence line. -/
def originalShearIncidenceNormalization : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S[X] :=
  (L).comp (fromOriginal W s b3 b4 b6 g3 g4 g6)
local notation "N" => originalShearIncidenceNormalization W s b3 b4 b6 S r hs h3 h4 hr g3 g4 g6

/-- The full contraction retains the horizontal normalization coordinate. -/
theorem originalShearIncidenceNormalization_x :
    N (WeierstrassIntegralChart.coord W 2 0) = X * (X + C a) := by
  change L (fromOriginal W s b3 b4 b6 g3 g4 g6 _) = _
  rw [fromOriginal_x, originalShearInitialLineMap_x]

/-- The full contraction retains the original vertical normalization coordinate. -/
theorem originalShearIncidenceNormalization_y :
    N (WeierstrassIntegralChart.coord W 2 1) = (X + C r) * (X * (X + C a)) := by
  change L (fromOriginal W s b3 b4 b6 g3 g4 g6 _) = _
  rw [fromOriginal_y, originalShearInitialLineMap_y]

/-- The complete incidence contraction has regular original horizontal coordinate. -/
theorem originalShearIncidenceNormalization_x_regular :
    IsRegular (N (WeierstrassIntegralChart.coord W 2 0)) := by
  rw [originalShearIncidenceNormalization_x]
  exact (monic_X.mul (monic_X_add_C a)).isRegular

end FLT.Mazur.WeierstrassModificationX
