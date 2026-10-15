/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationInverseIdeal

/-!
# The terminal inverse preserves every ideal, including deeper arithmetic powers

The factor multiplying the inverse coordinate is a unit. Ideal membership
therefore follows from the exact inverse equation for any chosen ideal.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (r : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
local notation "F" => terminalInversePolynomial W r I hI hrI ha

include hI hrI ha in
/-- The multiplier in the terminal inverse equation is a unit at every horizontal value. -/
theorem terminalInversePolynomial_multiplier_unit (z : R) :
    IsUnit (W.a₁ + r.eval z + r.eval z) := by
  have hm : r.eval z ∈ I := by
    simpa only [eval₂_id, Ideal.map_id] using
      NilpotentPolynomialInverse.eval₂_mem I (RingHom.id R) r hrI z
  have hn := NilpotentQuadraticRoot.element_nilpotent I hI (I.add_mem hm hm)
  have hu := hn.isUnit_add_right_of_commute ha (mul_comm _ _)
  simpa only [add_assoc, add_comm, add_left_comm] using hu

/-- Every original ideal, not only the nilpotent ideal, is preserved by the inverse. -/
theorem terminalInversePolynomial_eval_mem_ideal (J : Ideal R) (z : R) (hz : z ∈ J) :
    (F).eval z ∈ J := by
  have he : (F).eval z * (W.a₁ + r.eval ((F).eval z) + r.eval ((F).eval z)) = z := by
    simpa using terminalInversePolynomial_eval_equation W r I hI hrI ha z
  apply (J.unit_mul_mem_iff_mem
    (terminalInversePolynomial_multiplier_unit W r I hI hrI ha ((F).eval z))).mp
  rw [mul_comm, he]
  exact hz

end FLT.Mazur.WeierstrassDilatation
