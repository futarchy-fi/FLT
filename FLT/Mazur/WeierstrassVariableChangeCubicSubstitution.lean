/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeLinear

/-!
# The actual homogeneous cubic under polynomial substitution

The coordinate substitution carries the defining homogeneous polynomial to
a unit multiple of the transformed cubic. Consequently its principal ideal
is exactly the transformed cubic ideal, including the scheme structure.
-/

@[expose] public noncomputable section

open WeierstrassCurve MvPolynomial

namespace FLT.Mazur.WeierstrassVariableChangeLinear

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The homogeneous substitution is evaluation at the three specified forms. -/
theorem substitution_eq_aeval : ProjectiveSpace.linearSubstitution (linearMap C) =
    aeval (WeierstrassVariableChangeHomogeneous.coordinates
      (C.map (algebraMap R (MvPolynomial (Fin 3) R))) X) := by
  ext i : 1
  simpa only [aeval_X] using substitution_X C i

/-- The full polynomial identity, before passing to any quotient or point. -/
theorem substitution_polynomial :
    ProjectiveSpace.linearSubstitution (linearMap C) W.toProjective.polynomial =
      MvPolynomial.C ((C.u : R) ^ 6) * (C • W).toProjective.polynomial := by
  rw [substitution_eq_aeval]
  have h := WeierstrassVariableChangeHomogeneous.eval_polynomial
    (C.map (algebraMap R (MvPolynomial (Fin 3) R)))
    (W.map (algebraMap R (MvPolynomial (Fin 3) R))) X
  rw [map_variableChange, Projective.map_polynomial, Projective.map_polynomial,
    eval_map, eval_map] at h
  simpa only [aeval_def, algebraMap_eq, eval₂_eta, VariableChange.map,
    Units.coe_map, MonoidHom.coe_ofClass, map_pow] using h

/-- The principal defining ideal is carried to the transformed defining ideal. -/
theorem substitution_cubicIdeal :
    Ideal.map (ProjectiveSpace.linearSubstitution (linearMap C)).toRingHom
        (Ideal.span {W.toProjective.polynomial}) =
      Ideal.span {(C • W).toProjective.polynomial} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {ProjectiveSpace.linearSubstitution (linearMap C) W.toProjective.polynomial} = _
  rw [substitution_polynomial]
  exact Ideal.span_singleton_mul_left_unit
    ((C.u.isUnit.pow 6).map MvPolynomial.C)
    (C • W).toProjective.polynomial

end FLT.Mazur.WeierstrassVariableChangeLinear
