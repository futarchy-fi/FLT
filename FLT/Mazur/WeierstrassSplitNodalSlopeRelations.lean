/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalAdditionFormula

/-!
# Nodal slope identities over arbitrary commutative rings

Factoring the actual ordinary and reciprocal denominators allows cancellation
without a field or reducedness assumption. The resulting polynomial identities
show that the Laurent tangent parameters multiply under the addition formulas.
-/

@[expose] public section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {S : Type*} [CommRing S] {a r s l m : S}

/-- Both reciprocal chart relations determine the same slope parameter identity. -/
theorem splitNodalReciprocal_slope_relation
    (hl : m * (r ^ 2 * (r + a) - s ^ 2 * (s + a)) = r * (r + a) - s * (s + a))
    (hc : m * ((r * (r + a)) ^ 2 + r * (r + a) * (s * (s + a)) +
        (s * (s + a)) ^ 2 - a * (r ^ 2 * (r + a))) =
      r ^ 2 * (r + a) + s ^ 2 * (s + a) + a * (s * (s + a)))
    (hd : IsUnit (r ^ 2 * (r + a) - s ^ 2 * (s + a)) ∨
      IsUnit ((r * (r + a)) ^ 2 + r * (r + a) * (s * (s + a)) +
        (s * (s + a)) ^ 2 - a * (r ^ 2 * (r + a)))) :
    m * (r ^ 2 + r * s + s ^ 2 + a * (r + s)) = r + s + a := by
  rcases hd with hd | hd
  · have hf : (r - s) * (r ^ 2 + r * s + s ^ 2 + a * (r + s)) =
        r ^ 2 * (r + a) - s ^ 2 * (s + a) := by ring
    have hu := isUnit_of_mul_isUnit_left (hf.symm ▸ hd)
    apply hu.mul_right_inj.mp
    linear_combination hl
  · have hf : (r ^ 2 - r * s + s ^ 2 + a * s) *
        (r ^ 2 + r * s + s ^ 2 + a * (r + s)) =
        (r * (r + a)) ^ 2 + r * (r + a) * (s * (s + a)) +
          (s * (s + a)) ^ 2 - a * (r ^ 2 * (r + a)) := by ring
    have hu := isUnit_of_mul_isUnit_left (hf.symm ▸ hd)
    apply hu.mul_right_inj.mp
    linear_combination hc

/-- Both ordinary chart relations determine the same slope parameter identity. -/
theorem splitNodalOrdinary_slope_relation
    (hl : l * (r * (r + a) - s * (s + a)) = r ^ 2 * (r + a) - s ^ 2 * (s + a))
    (hc : l * (r ^ 2 * (r + a) + s ^ 2 * (s + a) + a * (s * (s + a))) =
      (r * (r + a)) ^ 2 + r * (r + a) * (s * (s + a)) +
        (s * (s + a)) ^ 2 - a * (r ^ 2 * (r + a)))
    (hd : IsUnit (r * (r + a) - s * (s + a)) ∨
      IsUnit (r ^ 2 * (r + a) + s ^ 2 * (s + a) + a * (s * (s + a)))) :
    l * (r + s + a) = r ^ 2 + r * s + s ^ 2 + a * (r + s) := by
  rcases hd with hd | hd
  · have hf : (r - s) * (r + s + a) = r * (r + a) - s * (s + a) := by ring
    have hu := isUnit_of_mul_isUnit_left (hf.symm ▸ hd)
    apply hu.mul_right_inj.mp
    linear_combination hl
  · have hf : (r ^ 2 - r * s + s ^ 2 + a * s) * (r + s + a) =
        r ^ 2 * (r + a) + s ^ 2 * (s + a) + a * (s * (s + a)) := by ring
    have hu := isUnit_of_mul_isUnit_left (hf.symm ▸ hd)
    apply hu.mul_right_inj.mp
    linear_combination hc

/-- The homogeneous reciprocal formula multiplies the tangent parameters polynomially. -/
theorem splitNodalReciprocal_parameter_identity
    (hm : m * (r ^ 2 + r * s + s ^ 2 + a * (r + s)) = r + s + a) :
    let v := reciprocalXYZ (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve S) (r * (r + a)) (s * (s + a))
      (r ^ 2 * (r + a)) m
    r * s * (v 1 + a * v 0) = (r + a) * (s + a) * v 1 := by
  dsimp [reciprocalXYZ, reciprocalH]
  linear_combination
    a * (-a ^ 2 * m ^ 2 - a * m ^ 2 * s - 2 * a * m + m ^ 2 * r ^ 2 -
      m ^ 2 * r * s - m * r - m * s - 1) * hm

/-- The ordinary formula multiplies the tangent parameters polynomially. -/
theorem splitNodalOrdinary_parameter_identity
    (hl : l * (r + s + a) = r ^ 2 + r * s + s ^ 2 + a * (r + s)) :
    let W := (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve S).toAffine
    let x := W.addX (r * (r + a)) (s * (s + a)) l
    let y := W.addY (r * (r + a)) (s * (s + a)) (r ^ 2 * (r + a)) l
    r * s * (y + a * x) = (r + a) * (s + a) * y := by
  dsimp [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, toAffine]
  linear_combination
    a * (a ^ 2 + 2 * a * l + a * s + l ^ 2 + l * r + l * s - r ^ 2 + r * s) * hl

end FLT.Mazur.WeierstrassIntegralChart
