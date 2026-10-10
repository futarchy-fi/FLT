/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The actual smooth Weierstrass parameter ring away from two

The coefficient ring is Z[a1,a2,a3,a4,a6,1/(2 Delta)]. Its universal equation
has unit discriminant. Specialization to every smooth Weierstrass equation
over a ring with two invertible is constructed and proved unique.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.UniversalWeierstrass

open MvPolynomial

/-- The five independent integral Weierstrass coefficients. -/
abbrev Coefficients := MvPolynomial (Fin 5) ℤ

/-- The universal integral equation, without any short-form restriction. -/
def equation : WeierstrassCurve Coefficients := ⟨X 0, X 1, X 2, X 3, X 4⟩

/-- Invert two and the discriminant; characteristic three is retained. -/
def denominator : Coefficients := 2 * equation.Δ

/-- The coordinate ring of the smooth Weierstrass parameter scheme. -/
abbrev ParameterRing := Localization.Away denominator

/-- The universal equation on the smooth parameter scheme. -/
def smoothEquation : WeierstrassCurve ParameterRing := equation.map (algebraMap _ _)

/-- Its discriminant is a unit by construction, rather than a supplied hypothesis. -/
theorem smoothEquation_discriminant : IsUnit smoothEquation.Δ := by
  rw [smoothEquation, WeierstrassCurve.map_Δ]
  exact (IsUnit.mul_iff.mp (show IsUnit
    (algebraMap Coefficients ParameterRing 2 * algebraMap Coefficients ParameterRing equation.Δ)
      from (map_mul (algebraMap Coefficients ParameterRing) 2 equation.Δ) ▸
        IsLocalization.Away.algebraMap_isUnit denominator)).2

/-- Two is invertible on the parameter scheme. -/
theorem parameter_two_isUnit : IsUnit (2 : ParameterRing) := by
  have h : IsUnit (algebraMap Coefficients ParameterRing (2 * equation.Δ)) :=
    IsLocalization.Away.algebraMap_isUnit denominator
  rw [map_mul, map_ofNat, IsUnit.mul_iff] at h
  exact h.1

variable {R T : Type} [CommRing R] [CommRing T]

/-- The coefficient map of a prescribed Weierstrass equation. -/
def coefficientMap (W : WeierstrassCurve R) : Coefficients →+* R :=
  eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/-- The universal polynomial equation specializes to the prescribed equation. -/
theorem equation_coefficientMap (W : WeierstrassCurve R) :
    equation.map (coefficientMap W) = W := by
  ext <;> simp [equation, coefficientMap]

/-- The inverted polynomial specializes to exactly twice the original discriminant. -/
theorem coefficientMap_denominator (W : WeierstrassCurve R) :
    coefficientMap W denominator = 2 * W.Δ := by
  rw [denominator, map_mul, map_ofNat, ← WeierstrassCurve.map_Δ,
    equation_coefficientMap]

/-- Every smooth equation with two invertible supplies an actual map from the parameter ring. -/
def specialize (W : WeierstrassCurve R) (h₂ : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) :
    ParameterRing →+* R :=
  IsLocalization.Away.lift denominator
    ((coefficientMap_denominator W).symm ▸ h₂.mul hΔ)

/-- Specialization has the prescribed coefficient map before localization. -/
@[simp] theorem specialize_algebraMap (W : WeierstrassCurve R)
    (h₂ : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) (a : Coefficients) :
    specialize W h₂ hΔ (algebraMap Coefficients ParameterRing a) = coefficientMap W a :=
  IsLocalization.Away.lift_eq _ _ _

/-- The actual universal smooth equation specializes to the original equation. -/
theorem smoothEquation_specialize (W : WeierstrassCurve R)
    (h₂ : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) :
    smoothEquation.map (specialize W h₂ hΔ) = W := by
  rw [smoothEquation, WeierstrassCurve.map_map]
  convert equation_coefficientMap W using 2
  exact IsLocalization.Away.lift_comp _ _

/-- Maps from the parameter ring are determined by the five coefficients. -/
@[ext] theorem parameter_hom_ext (f g : ParameterRing →+* R)
    (h : ∀ i : Fin 5, f (algebraMap Coefficients ParameterRing (X i)) =
      g (algebraMap Coefficients ParameterRing (X i))) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers denominator)
  apply MvPolynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · exact h

/-- Specialization commutes with every ring homomorphism, including residue maps. -/
theorem specialize_natural (W : WeierstrassCurve R) (h₂ : IsUnit (2 : R))
    (hΔ : IsUnit W.Δ) (f : R →+* T) (h₂' : IsUnit (2 : T))
    (hΔ' : IsUnit (W.map f).Δ) :
    f.comp (specialize W h₂ hΔ) = specialize (W.map f) h₂' hΔ' := by
  apply parameter_hom_ext
  intro i
  fin_cases i <;> simp [coefficientMap]

end FLT.Mazur.UniversalWeierstrass
