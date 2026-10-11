/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryConormalPolynomial

/-!
# Integral conormal errors on the original addition charts

The polynomial identities specialize through the actual addition algebra,
without replacing the integral equation by its split residue equation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b : Bool)
  (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
local notation "a" => algebraMap R S W.a₁
local notation "x" => f (ordinaryInputRight W b (coord W 2 0))
local notation "y" => f (ordinaryInputRight W b (coord W 2 1))
local notation "X" => f (ordinaryChartAddition W b (coord W 2 0))
local notation "Y" => f (ordinaryChartAddition W b (coord W 2 1))
local notation "l" => f (ordinaryChartSlope W b)

/-- The error in the first character, in the actual integral addition algebra. -/
theorem ordinarySpecialization_first_error :
    l * Y - (l + a) * y =
      -(X ^ 2 + x * X + x ^ 2 + algebraMap R S W.a₂ * (X + x) +
        algebraMap R S W.a₄) := by
  rw [ordinarySpecialization_coord, ordinarySpecialization_coord]
  exact ordinaryConormalPolynomial_first (W.map (algebraMap R S)) _ _ x y l
    (ordinarySpecialization_line W b f) (ordinarySpecialization_cubic W b f)

/-- The error in the opposite branch retains the original third coefficient. -/
theorem ordinarySpecialization_second_error :
    (l + a) * (Y + a * X) - l * (y + a * x) =
      -(X ^ 2 + x * X + x ^ 2 + algebraMap R S W.a₂ * (X + x) +
        algebraMap R S W.a₄ + a * algebraMap R S W.a₃) := by
  rw [ordinarySpecialization_coord, ordinarySpecialization_coord]
  exact ordinaryConormalPolynomial_second (W.map (algebraMap R S)) _ _ x y l
    (ordinarySpecialization_line W b f) (ordinarySpecialization_cubic W b f)

/-- The original base generator is fixed by both integral input and output maps. -/
theorem ordinarySpecialization_base_generator (s : R) :
    f (ordinaryChartAddition W b (algebraMap R _ s)) =
      f (ordinaryInputRight W b (algebraMap R _ s)) := by
  simp only [AlgHom.commutes]

end FLT.Mazur.WeierstrassIntegralChart
