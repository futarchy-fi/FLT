/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeDualProjectivePoints

/-!
# Dual projective points over an affine test ring

The scheme-point comparison holds after any coefficient homomorphism and
any compatible change of the finite free section coordinates. The polynomial
comparison is proved from the actual coefficient square of linear maps.
-/

@[expose] public noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FiniteFreeContragredient
open ProjectiveSpace
variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι κ : Type u} [Finite ι] [Finite κ]

/-- Evaluation after coefficient extension is the actual extended dual pairing. -/
lemma evaluate_linearForm_coefficient (φ : R →+* S) (w : ι →₀ R) (v : ι →₀ S) :
    eval₂ φ (fun i ↦ v i) (linearForm w) =
      dualCoordinates S ι (changeCoefficients φ w) v := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, eval₂_add, LinearMap.add_apply, hw, hz]
  | single i r => simp [smul_eq_C_mul, dualCoordinates_single_left]

/-- Pullback of a dual generator evaluates to the transported test-ring coordinate. -/
lemma evaluate_inverse_generator_coefficient (φ : R →+* S)
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ w, changeCoefficients φ (e w) = d (changeCoefficients φ w))
    (v : ι →₀ S) (j : κ) :
    eval₂ φ (fun i ↦ v i) (linearForm ((map e).symm (Finsupp.single j 1))) = d v j := by
  rw [evaluate_linearForm_coefficient,
    changeCoefficients_inverse φ (map e) (map d) (map_coefficient φ e d h),
    changeCoefficients_single, map_one]
  have hp := pairing d ((map d).symm (Finsupp.single j 1)) v
  simpa only [LinearEquiv.apply_symm_apply, dualCoordinates_single_left, one_mul] using hp.symm

/-- The graded polynomial pullback transports every test-ring section coordinate. -/
lemma evaluate_contragredient_coefficient (φ : R →+* S)
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ w, changeCoefficients φ (e w) = d (changeCoefficients φ w)) (v : ι →₀ S) :
    (eval₂Hom φ (fun i ↦ v i)).comp
        (linearGradedMap (map e).symm.toLinearMap).toRingHom =
      eval₂Hom φ (fun j ↦ d v j) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change eval₂ φ (fun i ↦ v i) (linearSubstitution (map e).symm.toLinearMap (C r)) = _
    simp
  · intro j
    change eval₂ φ (fun i ↦ v i) (linearSubstitution (map e).symm.toLinearMap (X j)) = _
    rw [linearSubstitution_X]
    exact (evaluate_inverse_generator_coefficient φ e d h v j).trans (eval₂_X φ _ j).symm

/-- Actual projective points transform by section coordinates over the test ring. -/
lemma unitChartPoint_transport_coefficient (φ : R →+* S)
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ w, changeCoefficients φ (e w) = d (changeCoefficients φ w))
    (v : ι →₀ S) (i : ι) (j : κ) (a b : Sˣ) (hi : v i = a) (hj : d v j = b) :
    unitChartPoint R ι φ (fun k ↦ v k) i a hi ≫ (linearIso (map e)).hom =
      unitChartPoint R κ φ (fun k ↦ d v k) j b hj :=
  unitChartPoint_linearIso_of_eval (map e) φ _ _
    (evaluate_contragredient_coefficient φ e d h v) i j a b hi hj

end FLT.Mazur.FiniteFreeContragredient
