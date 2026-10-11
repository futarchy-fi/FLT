/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalTangentCharacters
public import FLT.Mazur.WeierstrassAdditionOutputFamilies

/-!
# Tangent characters of the original ordinary addition chart

Specializations of the actual addition algebra have the computed two characters.
Only the input coordinates and their square-zero relations are hypotheses.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (a : R) (r q : Sˣ) (b : Bool)
local notation "W" => WeierstrassCurve.mk a 0 0 0 0
variable (f : additionChartRing (WeierstrassCurve.mk a 0 0 0 0)
  (ordinaryIndex b) →ₐ[R] S)
local notation "g" => additionChartAlgRestriction W (ordinaryIndex b)
local notation "x" => f (g (productX₂ W))
local notation "y" => f (g (productY₂ W))

/-- The original chart's slope specializes to the uniquely determined node secant. -/
theorem splitNodalTangentChart_slope
    (hx₁ : f (g (productX₁ W)) = (r : S) * q)
    (hy₁ : f (g (productY₁ W)) = (r : S) ^ 2 * q)
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) :
    f (ordinaryChartSlope W b) = splitNodalTangentSlope r q x y := by
  apply splitNodalTangentSlope_unique r q x y hxx hxy
  have h := congrArg f (ordinaryChartSlope_line W b)
  simpa only [map_mul, map_secantDenominator, map_verticalSecantDenominator,
    map_sub, hx₁, hy₁] using h

/-- The original addition map scales the first tangent branch function. -/
theorem splitNodalTangentChart_first_character
    (hq : (q : S) = (r : S) + algebraMap R S a)
    (hx₁ : f (g (productX₁ W)) = (r : S) * q)
    (hy₁ : f (g (productY₁ W)) = (r : S) ^ 2 * q)
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    (r : S) * f (ordinaryChartAddition W b (coord W 2 1)) = (q : S) * y := by
  rw [ordinaryChartAddition_map_coord, Matrix.cons_val_one, Matrix.cons_val_zero,
    hx₁, hy₁, splitNodalTangentChart_slope a r q b f hx₁ hy₁ hxx hxy]
  simpa only [WeierstrassCurve.map, map_zero] using
    splitNodalTangent_first_character (algebraMap R S a) r q x y hq hxx hxy hyy

/-- The original addition map scales the opposite tangent branch function reciprocally. -/
theorem splitNodalTangentChart_second_character
    (hq : (q : S) = (r : S) + algebraMap R S a)
    (hx₁ : f (g (productX₁ W)) = (r : S) * q)
    (hy₁ : f (g (productY₁ W)) = (r : S) ^ 2 * q)
    (hxx : x ^ 2 = 0) (hxy : x * y = 0) (hyy : y ^ 2 = 0) :
    (q : S) * f (ordinaryChartAddition W b
        (coord W 2 1 + algebraMap R _ a * coord W 2 0)) =
      (r : S) * (y + algebraMap R S a * x) := by
  simp only [map_add, map_mul, AlgHom.commutes, ordinaryChartAddition_map_coord,
    Matrix.cons_val_one, Matrix.cons_val_zero, hx₁, hy₁,
    splitNodalTangentChart_slope a r q b f hx₁ hy₁ hxx hxy]
  simpa only [WeierstrassCurve.map, map_zero] using
    splitNodalTangent_second_character (algebraMap R S a) r q x y hq hxx hxy hyy

end FLT.Mazur.WeierstrassIntegralChart
