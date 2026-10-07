/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffinePolynomialFormula
public import FLT.Mazur.WeierstrassAdditionOutputFamilies
public import FLT.Mazur.WeierstrassProjectiveAdditionChart

/-!
# Polynomial scaling on the four actual affine addition domains

Specialize the integral homogeneous identities to the constructed ordinary
and reciprocal slope maps. The resulting factors compare the polynomial law
to each actual normalized affine addition law.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- On affine inputs the universal polynomial law evaluates at normalized affine vectors. -/
theorem affinePolynomial_map (f : AffineProduct W →ₐ[R] S) :
    f ∘ chartProductAdditionCoordinates W 2 2 =
      (W.map (algebraMap R S)).toProjective.addXYZ
        ![f (productX₁ W), f (productY₁ W), 1]
        ![f (productX₂ W), f (productY₂ W), 1] := by
  have hl : f ∘ chartProductLeft W 2 2 ∘ coord W 2 =
      ![f (productX₁ W), f (productY₁ W), 1] := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change f (productLeft W (coord W 2 2)) = 1
      rw [coord_self, map_one, map_one]
  have hr : f ∘ chartProductRight W 2 2 ∘ coord W 2 =
      ![f (productX₂ W), f (productY₂ W), 1] := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change f (productRight W (coord W 2 2)) = 1
      rw [coord_self, map_one, map_one]
  exact (chartProductAdditionCoordinates_map W 2 2 f).trans
    (congrArg₂ (W.map (algebraMap R S)).toProjective.addXYZ hl hr)

/-- Both ordinary chart maps scale to the polynomial law by the cube of the x-difference. -/
theorem ordinaryPolynomial_scaled (b : Bool) (i : Fin 3) :
    additionChartAlgRestriction W (ordinaryIndex b) (chartProductAdditionCoordinates W 2 2 i) =
      additionChartAlgRestriction W (ordinaryIndex b) (secantDenominator W) ^ 3 *
        ordinaryChartAddition W b (coord W 2 i) := by
  let f := additionChartAlgRestriction W (ordinaryIndex b)
  have hl := ordinaryChartSlope_line W b
  simp only [map_secantDenominator, map_verticalSecantDenominator] at hl
  have hs := affinePolynomial_ordinary (W.map (algebraMap R _))
    (productLeft_equation W f) (productRight_equation W f) hl
  have hp := congrFun (affinePolynomial_map W f) i
  rw [hs] at hp
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul,
    ordinaryChartAddition_coord, map_secantDenominator] using hp

/-- The reciprocal chart normalization cancels its homogeneous y-coordinate. -/
theorem reciprocalChartInverse_mul_coordinates (b : Bool) :
    reciprocalChartInverse W b *
      reciprocalCoordinates W (additionChartAlgRestriction W (reciprocalIndex b))
        (reciprocalChartSlope W b) 1 = 1 := by
  have h := reciprocalChartAddition_coord W b 1
  rw [coord_self, map_one] at h
  exact h.symm

/-- Homogeneous factor for comparison with the normalized reciprocal output. -/
def reciprocalPolynomialFactor (b : Bool) : additionChartRing W (reciprocalIndex b) :=
  additionChartAlgRestriction W (reciprocalIndex b) (verticalSecantDenominator W) ^ 3 *
    reciprocalCoordinates W (additionChartAlgRestriction W (reciprocalIndex b))
      (reciprocalChartSlope W b) 1

/-- Both reciprocal chart maps scale to the polynomial law, including at slope zero. -/
theorem reciprocalPolynomial_scaled (b : Bool) (i : Fin 3) :
    additionChartAlgRestriction W (reciprocalIndex b)
        (chartProductAdditionCoordinates W 2 2 i) =
      reciprocalPolynomialFactor W b * reciprocalChartAddition W b (coord W 1 i) := by
  let f := additionChartAlgRestriction W (reciprocalIndex b)
  have hl := reciprocalChartSlope_line W b
  simp only [map_secantDenominator, map_verticalSecantDenominator] at hl
  have hs := affinePolynomial_reciprocal (W.map (algebraMap R _))
    (productLeft_equation W f) (productRight_equation W f) hl
  have hp := congrFun (affinePolynomial_map W f) i
  rw [hs] at hp
  change f (chartProductAdditionCoordinates W 2 2 i) =
    (f (productY₁ W) - f (productY₂ W)) ^ 3 *
      reciprocalCoordinates W f (reciprocalChartSlope W b) i at hp
  rw [hp, reciprocalPolynomialFactor, reciprocalChartAddition_coord,
    map_verticalSecantDenominator]
  have hi := reciprocalChartInverse_mul_coordinates W b
  linear_combination -(f (productY₁ W) - f (productY₂ W)) ^ 3 *
    reciprocalCoordinates W f (reciprocalChartSlope W b) i * hi

end FLT.Mazur.WeierstrassIntegralChart
