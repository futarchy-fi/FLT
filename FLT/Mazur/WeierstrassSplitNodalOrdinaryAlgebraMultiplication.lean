/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalOrdinaryParameter
public import FLT.Mazur.WeierstrassSplitNodalChartParameters

/-!
# Ordinary addition multiplies actual Laurent units over arbitrary rings

Common affine and smooth chart inputs suffice to force a unit output ordinate and identify
its smooth chart homomorphism with the product unit evaluation. This equality holds over
nonreduced algebras, rather than only on field-valued points.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (a : Rˣ) (b : Bool)
  (f : additionChartRing (splitNodalEquation a) (ordinaryIndex b) →ₐ[R] S)
  (p q : Coordinate (splitNodalEquation a) 1 →ₐ[R] S)
  (hp : ∀ i, f (ordinaryInputLeft (splitNodalEquation a) b
      (coord (splitNodalEquation a) 2 i)) =
    f (ordinaryInputLeft (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1)) *
      p (coord (splitNodalEquation a) 1 i))
  (hq : ∀ i, f (ordinaryInputRight (splitNodalEquation a) b
      (coord (splitNodalEquation a) 2 i)) =
    f (ordinaryInputRight (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1)) *
      q (coord (splitNodalEquation a) 1 i))

include hp hq

/-- Both smooth common inputs force the original ordinary output ordinate to be a unit. -/
theorem splitNodalOrdinary_output_y_isUnit :
    IsUnit (f (ordinaryChartAddition (splitNodalEquation a) b
      (coord (splitNodalEquation a) 2 1))) := by
  obtain ⟨r, hra, hx₁, hy₁, _⟩ := splitNodalAffineChart_exists_parameter a
    (f.comp (ordinaryInputLeft (splitNodalEquation a) b)) p hp
  obtain ⟨s, hsa, hx₂, hy₂, _⟩ := splitNodalAffineChart_exists_parameter a
    (f.comp (ordinaryInputRight (splitNodalEquation a) b)) q hq
  exact splitNodalOrdinary_specialized_y_isUnit a b f r s hx₁ hy₁ hx₂ hy₂
    r.isUnit s.isUnit hra hsa

variable (t : Coordinate (splitNodalEquation a) 1 →ₐ[R] S)
  (ht : ∀ i, f (ordinaryChartAddition (splitNodalEquation a) b
      (coord (splitNodalEquation a) 2 i)) =
    f (ordinaryChartAddition (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1)) *
      t (coord (splitNodalEquation a) 1 i))

include ht

/-- The smooth chart of the ordinary output has the product of the actual input units. -/
theorem splitNodalOrdinary_chartUnit_mul :
    splitNodalChartUnit a t = splitNodalChartUnit a p * splitNodalChartUnit a q := by
  obtain ⟨r, _, hx₁, hy₁, hr⟩ := splitNodalAffineChart_exists_parameter a
    (f.comp (ordinaryInputLeft (splitNodalEquation a) b)) p hp
  obtain ⟨s, _, hx₂, hy₂, hs⟩ := splitNodalAffineChart_exists_parameter a
    (f.comp (ordinaryInputRight (splitNodalEquation a) b)) q hq
  have h := splitNodalOrdinary_specialized_parameter a b f r s hx₁ hy₁ hx₂ hy₂
  have hu := splitNodalOrdinary_output_y_isUnit a b f p q hp hq
  have hp' := splitNodalChartUnit_mul_slope a p r hr
  have hq' := splitNodalChartUnit_mul_slope a q s hs
  apply Units.ext
  rw [Units.val_mul, splitNodalChartUnit_val]
  apply (r.isUnit.mul s.isUnit).mul_right_inj.mp
  apply hu.mul_right_inj.mp
  linear_combination h -
    (r : S) * s * algebraMap R S a * ht 0 -
    f (ordinaryChartAddition (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1)) *
      (((s : S) + algebraMap R S a) * hp' +
        (r : S) * (splitNodalChartUnit a p : S) * hq')

/-- The entire smooth output homomorphism is evaluation at the product unit. -/
theorem splitNodalOrdinary_chart_multiplication :
    t = splitNodalUnitChart a (splitNodalChartUnit a p * splitNodalChartUnit a q) := by
  rw [← splitNodalOrdinary_chartUnit_mul a b f p q hp hq t ht,
    splitNodalUnitChart_chartUnit]

end FLT.Mazur.WeierstrassIntegralChart
