/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import FLT.Mazur.UniversalWeierstrassParameter

/-!
# The smooth one-gon boundary parameter in the original Weierstrass atlas

On the locus where two, the smoothing parameter, and its complementary
factor are units, the original boundary equation gives an actual point of
the smooth coefficient scheme. This point retains all five coefficients
and commutes with coefficient change.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OneGonSmoothing
variable {R S : Type} [CommRing R] [CommRing S]
  (t : R) (h₂ : IsUnit (2 : R)) (ht : IsUnit t) (hf : IsUnit (1 + 432 * t))

/-- The boundary equation has unit discriminant on its actual smooth parameter locus. -/
theorem smooth_discriminant (ht : IsUnit t) (hf : IsUnit (1 + 432 * t)) :
    IsUnit (equation t).Δ := by
  rw [equation_discriminant]
  exact ht.neg.mul hf

/-- The actual coefficient point of the original smooth Weierstrass parameter scheme. -/
def smoothParameter : UniversalWeierstrass.ParameterRing →+* R :=
  UniversalWeierstrass.specialize (equation t) h₂ (smooth_discriminant t ht hf)

/-- Specialization retains the original boundary equation, including in characteristic three. -/
theorem smoothParameter_equation :
    UniversalWeierstrass.smoothEquation.map (smoothParameter t h₂ ht hf) = equation t :=
  UniversalWeierstrass.smoothEquation_specialize _ _ _

/-- The boundary parameter map retains each of the original five coefficients. -/
theorem smoothParameter_coeff (i : Fin 5) :
    smoothParameter t h₂ ht hf
      (algebraMap UniversalWeierstrass.Coefficients UniversalWeierstrass.ParameterRing
        (MvPolynomial.X i)) = ![-1, 0, 0, 0, t] i := by
  rw [smoothParameter, UniversalWeierstrass.specialize_algebraMap]
  simp [UniversalWeierstrass.coefficientMap, equation]

/-- The smooth boundary point commutes with every specified coefficient map. -/
theorem smoothParameter_natural (f : R →+* S) (h₂' : IsUnit (2 : S))
    (ht' : IsUnit (f t)) (hf' : IsUnit (1 + 432 * f t)) :
    f.comp (smoothParameter t h₂ ht hf) = smoothParameter (f t) h₂' ht' hf' := by
  apply UniversalWeierstrass.parameter_hom_ext
  intro i
  rw [RingHom.comp_apply, smoothParameter_coeff, smoothParameter_coeff]
  fin_cases i <;> simp

/-- A coefficient point with this exact equation is the constructed boundary parameter. -/
theorem smoothParameter_unique (g : UniversalWeierstrass.ParameterRing →+* R)
    (hg : UniversalWeierstrass.smoothEquation.map g = equation t) :
    g = smoothParameter t h₂ ht hf := by
  apply UniversalWeierstrass.parameter_hom_ext
  intro i
  rw [smoothParameter_coeff]
  fin_cases i
  · exact congrArg WeierstrassCurve.a₁ hg
  · exact congrArg WeierstrassCurve.a₂ hg
  · exact congrArg WeierstrassCurve.a₃ hg
  · exact congrArg WeierstrassCurve.a₄ hg
  · exact congrArg WeierstrassCurve.a₆ hg

end FLT.Mazur.OneGonSmoothing
