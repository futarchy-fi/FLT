/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureSquare

/-!
# Recovering full node identifications from stationary punctures

Both original punctures jointly detect the complete node algebra. A full
factor with identity substitutions is the canonical equal-parameter map.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R]

/-- Identity on both punctures identifies the entire factor, including its closed node. -/
theorem nodeFactor_eq_parameter_of_punctures (s t : R) (h : s = t)
    (f : ChartRing s ≃ₐ[R] ChartRing t)
    (hf : ∀ b, (punctureLaurentMap t b).comp f.toAlgHom = punctureLaurentMap s b) :
    f = nodeParameterEquiv s t h := by
  ext z : 1
  apply punctureLaurent_ext t
  intro b
  have hf' := AlgHom.congr_fun (hf b) z
  have hi := AlgHom.congr_fun (punctureLaurentMap_parameter s t h b) z
  exact hf'.trans hi.symm

/-- Equality of both full substitutions identifies arbitrary whole-node factors. -/
theorem nodeFactor_eq_of_punctures (s t : R)
    (f g : ChartRing s ≃ₐ[R] ChartRing t)
    (h : ∀ b, (punctureLaurentMap t b).comp f.toAlgHom =
      (punctureLaurentMap t b).comp g.toAlgHom) : f = g := by
  ext z : 1
  exact punctureLaurent_ext t _ _ (fun b ↦ AlgHom.congr_fun (h b) z)

end FLT.Mazur.PolygonSmoothing
