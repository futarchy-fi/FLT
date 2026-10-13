/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassParameter
public import Mathlib.Data.ZMod.Basic

/-!
# Smooth Weierstrass parameters in every characteristic

Only the discriminant is inverted. This supplies the coefficient foundation for
charts in characteristic two; the existing away-from-two chart is a specialization.
No auxiliary level coverage is asserted here.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.IntegralWeierstrassParameter
open MvPolynomial
open UniversalWeierstrass (Coefficients equation coefficientMap equation_coefficientMap)

/-- The smooth coefficient ring retains all residue characteristics. -/
abbrev SmoothRing := Localization.Away equation.Δ

/-- The original five-coefficient equation over the discriminant localization. -/
def smoothEquation : WeierstrassCurve SmoothRing := equation.map (algebraMap _ _)

/-- The discriminant is a unit without inverting any integer. -/
theorem smoothEquation_discriminant : IsUnit smoothEquation.Δ := by
  rw [smoothEquation, WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit equation.Δ

variable {R S : Type} [CommRing R] [CommRing S]

/-- Every smooth equation supplies an actual specialization in every characteristic. -/
def specialize (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) : SmoothRing →+* R :=
  IsLocalization.Away.lift equation.Δ (show IsUnit (coefficientMap W equation.Δ) by
    rw [← WeierstrassCurve.map_Δ, equation_coefficientMap]
    exact hΔ)

/-- The specialization retains the prescribed original coefficients. -/
@[simp] theorem specialize_algebraMap (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
    (a : Coefficients) :
    specialize W hΔ (algebraMap Coefficients SmoothRing a) = coefficientMap W a :=
  IsLocalization.Away.lift_eq _ _ _

/-- The actual universal equation specializes to the original five-coefficient equation. -/
theorem smoothEquation_specialize (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) :
    smoothEquation.map (specialize W hΔ) = W := by
  rw [smoothEquation, WeierstrassCurve.map_map]
  convert equation_coefficientMap W using 2
  exact IsLocalization.Away.lift_comp _ _

/-- Five coefficient values determine a map from the all-characteristic smooth parameter ring. -/
@[ext] theorem smoothRing_hom_ext (f g : SmoothRing →+* R)
    (h : ∀ i : Fin 5, f (algebraMap Coefficients SmoothRing (X i)) =
      g (algebraMap Coefficients SmoothRing (X i))) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers equation.Δ)
  apply MvPolynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · exact h

/-- Specialization commutes with arbitrary ring homomorphisms, including characteristic change. -/
theorem specialize_natural (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
    (f : R →+* S) (hΔ' : IsUnit (W.map f).Δ) :
    f.comp (specialize W hΔ) = specialize (W.map f) hΔ' := by
  apply smoothRing_hom_ext
  intro i
  fin_cases i <;> simp [coefficientMap]

/-- The existing away-from-two coefficient ring is an actual specialization of this one. -/
def awayFromTwo : SmoothRing →+* UniversalWeierstrass.ParameterRing :=
  specialize UniversalWeierstrass.smoothEquation
    UniversalWeierstrass.smoothEquation_discriminant

/-- Restriction to the existing chart retains its original equation exactly. -/
theorem smoothEquation_awayFromTwo :
    smoothEquation.map awayFromTwo = UniversalWeierstrass.smoothEquation :=
  smoothEquation_specialize _ _

/-- A smooth characteristic-two equation with its original nonzero linear y coefficient. -/
def characteristicTwoEquation : WeierstrassCurve (ZMod 2) := ⟨0, 0, 1, 0, 0⟩

/-- This characteristic-two equation has unit discriminant. -/
theorem characteristicTwo_discriminant : IsUnit characteristicTwoEquation.Δ := by
  have h : characteristicTwoEquation.Δ = 1 := by decide
  rw [h]
  exact isUnit_one

/-- The new parameter ring has an actual characteristic-two point. -/
def characteristicTwoMap : SmoothRing →+* ZMod 2 :=
  specialize characteristicTwoEquation characteristicTwo_discriminant

/-- That point retains the actual characteristic-two cubic. -/
theorem characteristicTwo_specialization :
    smoothEquation.map characteristicTwoMap = characteristicTwoEquation :=
  smoothEquation_specialize _ _

/-- The all-characteristic ring has not accidentally inverted two. -/
theorem smoothRing_two_not_isUnit : ¬ IsUnit (2 : SmoothRing) := by
  intro h
  have hh := h.map characteristicTwoMap
  rw [map_ofNat] at hh
  exact hh.ne_zero (by decide)

end FLT.Mazur.IntegralWeierstrassParameter
