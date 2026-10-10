/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationBaseChange
public import FLT.Mazur.WeierstrassDilatationUnitComparison
public import FLT.Mazur.WeierstrassChartBaseChange

/-!
# The actual generic fiber of the divided chart

After any coefficient extension that makes the scale invertible, the original
and divided charts have isomorphic tensor algebras. The comparison keeps the
original coordinates, multiplied by the exact scaling parameter.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.WeierstrassDilatation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (S : Type u) [CommRing S] [Algebra R S] (hs : IsUnit (algebraMap R S s))

include h3 h4 h6 in
/-- The actual contraction on affine algebras is bijective whenever its scale is a unit. -/
theorem fromOriginal_bijective_of_unit (hs : IsUnit s) :
    Function.Bijective (fromOriginal W s b3 b4 b6 h3 h4 h6) := by
  obtain ⟨t, rfl⟩ := hs
  exact (originalEquiv W t b3 b4 b6 h3 h4 h6).bijective

/-- The explicit unit comparison for the actual specialized coefficients. -/
def specializedOriginalEquiv :
    WeierstrassIntegralChart.Coordinate (W.map (algebraMap R S)) 2 ≃ₐ[S]
      ExtendedCoordinate W s b3 b4 b6 S := by
  have h3' : (W.map (algebraMap R S)).a₃ = algebraMap R S s * algebraMap R S b3 := by
    simp only [WeierstrassCurve.map_a₃, h3, map_mul]
  have h4' : (W.map (algebraMap R S)).a₄ = algebraMap R S s * algebraMap R S b4 := by
    simp only [WeierstrassCurve.map_a₄, h4, map_mul]
  have h6' : (W.map (algebraMap R S)).a₆ = algebraMap R S s ^ 2 * algebraMap R S b6 := by
    simp only [WeierstrassCurve.map_a₆, h6, map_mul, map_pow]
  exact AlgEquiv.ofBijective
    (fromOriginal (W.map (algebraMap R S)) (algebraMap R S s)
      (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) h3' h4' h6')
    (fromOriginal_bijective_of_unit _ _ _ _ _ h3' h4' h6' hs)

/-- The first specialized coordinate retains the precise original scaling. -/
theorem specializedOriginalEquiv_x :
    specializedOriginalEquiv W s b3 b4 b6 h3 h4 h6 S hs
      (WeierstrassIntegralChart.coord (W.map (algebraMap R S)) 2 0) =
      algebraMap S _ (algebraMap R S s) *
        x (W.map (algebraMap R S))
          (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) := by
  simp [specializedOriginalEquiv, fromOriginal, WeierstrassIntegralChart.evaluation_coord]

/-- The second specialized coordinate retains the precise original scaling. -/
theorem specializedOriginalEquiv_y :
    specializedOriginalEquiv W s b3 b4 b6 h3 h4 h6 S hs
      (WeierstrassIntegralChart.coord (W.map (algebraMap R S)) 2 1) =
      algebraMap S _ (algebraMap R S s) *
        y (W.map (algebraMap R S))
          (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) := by
  simp [specializedOriginalEquiv, fromOriginal, WeierstrassIntegralChart.evaluation_coord]

/-- The original and divided charts have the same actual fiber wherever the scale is invertible. -/
def genericFiberEquiv : WeierstrassIntegralChart.ChartScalarExtension S W 2 ≃ₐ[S]
    ScalarExtension W s b3 b4 b6 S :=
  ((WeierstrassIntegralChart.chartBaseChangeEquiv S W 2).trans
    (specializedOriginalEquiv W s b3 b4 b6 h3 h4 h6 S hs)).trans
      (baseChangeEquiv W s b3 b4 b6 S).symm

/-- In a fraction field every nonzero scaling parameter gives the actual generic comparison. -/
def fractionFieldEquiv (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (hs : s ≠ 0) :
    WeierstrassIntegralChart.ChartScalarExtension K W 2 ≃ₐ[K]
      ScalarExtension W s b3 b4 b6 K :=
  genericFiberEquiv W s b3 b4 b6 h3 h4 h6 K
    (isUnit_iff_ne_zero.mpr (fun h =>
      hs ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))))

end FLT.Mazur.WeierstrassDilatation
