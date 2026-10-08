/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalReciprocalParameter
public import FLT.Mazur.WeierstrassSplitNodalChartParameters

/-!
# Reciprocal addition multiplies actual Laurent units over arbitrary rings

Common affine and smooth chart inputs suffice to identify the entire reciprocal
output homomorphism with the product unit evaluation. This equality holds over
nonreduced algebras, rather than only on field-valued points.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (a : Rˣ) (b : Bool)
  (f : additionChartRing (splitNodalEquation a) (reciprocalIndex b) →ₐ[R] S)
  (p q : Coordinate (splitNodalEquation a) 1 →ₐ[R] S)
  (hp : ∀ i, f (reciprocalInputLeft (splitNodalEquation a) b
      (coord (splitNodalEquation a) 2 i)) =
    f (reciprocalInputLeft (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1)) *
      p (coord (splitNodalEquation a) 1 i))
  (hq : ∀ i, f (reciprocalInputRight (splitNodalEquation a) b
      (coord (splitNodalEquation a) 2 i)) =
    f (reciprocalInputRight (splitNodalEquation a) b (coord (splitNodalEquation a) 2 1)) *
      q (coord (splitNodalEquation a) 1 i))

include hp hq

/-- The output Laurent unit is the product of the actual common-input Laurent units. -/
theorem splitNodalReciprocal_chartUnit_mul :
    splitNodalChartUnit a (f.comp (reciprocalChartAddition (splitNodalEquation a) b)) =
      splitNodalChartUnit a p * splitNodalChartUnit a q := by
  obtain ⟨r, _, hx₁, hy₁, hr⟩ := splitNodalAffineChart_exists_parameter a
    (f.comp (reciprocalInputLeft (splitNodalEquation a) b)) p hp
  obtain ⟨s, _, hx₂, hy₂, hs⟩ := splitNodalAffineChart_exists_parameter a
    (f.comp (reciprocalInputRight (splitNodalEquation a) b)) q hq
  have h := splitNodalReciprocal_specialized_parameter a b f r s hx₁ hy₁ hx₂ hy₂
  have hp' := splitNodalChartUnit_mul_slope a p r hr
  have hq' := splitNodalChartUnit_mul_slope a q s hs
  apply Units.ext
  rw [Units.val_mul, splitNodalChartUnit_val]
  apply (r.isUnit.mul s.isUnit).mul_right_inj.mp
  change (r : S) * s * (1 + algebraMap R S a *
    f (reciprocalChartAddition (splitNodalEquation a) b
      (coord (splitNodalEquation a) 1 0))) = _
  calc
    _ = ((r : S) + algebraMap R S a) * ((s : S) + algebraMap R S a) := h
    _ = ((r : S) * (splitNodalChartUnit a p : S)) *
        ((s : S) * (splitNodalChartUnit a q : S)) := by rw [hp', hq']
    _ = _ := by ring

/-- The full original reciprocal output homomorphism is unit product evaluation. -/
theorem splitNodalReciprocal_chart_multiplication :
    f.comp (reciprocalChartAddition (splitNodalEquation a) b) =
      splitNodalUnitChart a (splitNodalChartUnit a p * splitNodalChartUnit a q) := by
  rw [← splitNodalReciprocal_chartUnit_mul a b f p q hp hq,
    splitNodalUnitChart_chartUnit]

end FLT.Mazur.WeierstrassIntegralChart
