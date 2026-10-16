/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BivariateCoordinateDifference

/-!
# Explicit coordinate errors after clearing a polynomial fraction

A fraction identity at the target coordinates gives a cross-multiplied source
error with explicit coefficients. Neither denominator invertibility nor
cancellation in the coefficient ring is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BivariateCoordinateDifference
variable {A R : Type*} [CommRing A] [CommRing R]

/-- Cross-multiply a polynomial fraction while keeping both coordinate-error coefficients. -/
theorem fraction_evaluation_sub (f : A →+* R) (p d : MvPolynomial (Fin 2) A)
    (x y : Fin 2 → R) (a : R)
    (ha : a * MvPolynomial.eval₂Hom f x d = MvPolynomial.eval₂Hom f x p) :
    a * MvPolynomial.eval₂Hom f y d - MvPolynomial.eval₂Hom f y p =
      (leftCoefficient f p x y - a * leftCoefficient f d x y) * (x 0 - y 0) +
        (rightCoefficient f p x y - a * rightCoefficient f d x y) * (x 1 - y 1) := by
  calc
    _ = (MvPolynomial.eval₂Hom f x p - MvPolynomial.eval₂Hom f y p) -
        a * (MvPolynomial.eval₂Hom f x d - MvPolynomial.eval₂Hom f y d) := by
      rw [← ha]
      ring
    _ = _ := by rw [evaluation_sub, evaluation_sub]; ring

/-- Restrict an exact polynomial error identity through any ring homomorphism. -/
theorem fraction_error_of_differences {S : Type*} [CommRing S] (ρ : R →+* S)
    (p d p₀ d₀ lp ld rp rd dx dy : R) (a : S)
    (hp : p - p₀ = lp * dx + rp * dy) (hd : d - d₀ = ld * dx + rd * dy)
    (ha : a * ρ d = ρ p) :
    a * ρ d₀ - ρ p₀ =
      (ρ lp - a * ρ ld) * ρ dx + (ρ rp - a * ρ rd) * ρ dy := by
  have hp' := congrArg ρ hp
  have hd' := congrArg ρ hd
  simp only [map_sub, map_add, map_mul] at hp' hd'
  calc
    _ = (ρ p - ρ p₀) - a * (ρ d - ρ d₀) := by rw [← ha]; ring
    _ = _ := by rw [hp', hd']; ring

end FLT.Mazur.BivariateCoordinateDifference
