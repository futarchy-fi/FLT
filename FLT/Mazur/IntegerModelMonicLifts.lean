/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FixedModelElementLifts
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Lifting monic polynomial witnesses to coefficient models

Only the lower coefficients are lifted; the leading coefficient stays one.
This retains monicity even when recovery is not injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

namespace FLT.Mazur.Approximation

universe u v

/-- Finitely many monic polynomials lift to monic polynomials over a common model. -/
theorem exists_integer_model_monic_lifts {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {n m : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    {I : Type v} [Finite I] (p : I → B[X]) (hp : ∀ i, (p i).Monic)
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ _h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S,
        ∃ q : I → (P.ModelOfHasCoeffs S)[X],
          (∀ i, (q i).Monic) ∧
          ∀ i, (q i).map (integerModelRecoveryHom P).toRingHom = p i := by
  classical
  let J := (i : I) × Fin (p i).natDegree
  obtain ⟨S, hS, hsS, h, hP, b, hb⟩ := exists_fixed_model_element_lifts P A₀
    (fun j : J ↦ (p j.1).coeff j.2) s hs
  let := hP
  have hb' (j : J) : (integerModelRecoveryHom P).toRingHom (b j) =
      (p j.1).coeff j.2 := hb j
  let q := fun i ↦ (X : (P.ModelOfHasCoeffs S)[X]) ^ (p i).natDegree +
    ∑ j : Fin (p i).natDegree, C (b ⟨i, j⟩) * X ^ (j : ℕ)
  refine ⟨S, hS, hsS, h, hP, q, fun i ↦ ?_, fun i ↦ ?_⟩
  · exact monic_X_pow_add (degree_sum_fin_lt _)
  · change (q i).map (integerModelRecoveryHom P).toRingHom = p i
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      hb']
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ C ((p i).coeff j) * X ^ j),
      ← (hp i).as_sum]

end FLT.Mazur.Approximation
