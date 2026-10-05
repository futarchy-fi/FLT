/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Solving a cubic with small higher coefficients

Over a Henselian local ring, a cubic with unit linear coefficient and higher
coefficients in the maximal ideal has a root. A reciprocal monic cubic
reduces this to the monic form of Hensel's lemma, even if the constant
coefficient vanishes or the original leading coefficient is not a unit.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
  [HenselianRing R (maximalIdeal R)]

/-- A unit linear coefficient and small higher coefficients suffice to solve a cubic. -/
theorem exists_root_small_cubic (c₃ c₂ c₁ c₀ : R)
    (h₃ : c₃ ∈ maximalIdeal R) (h₂ : c₂ ∈ maximalIdeal R) (h₁ : IsUnit c₁) :
    ∃ a : R, c₃ * a ^ 3 + c₂ * a ^ 2 + c₁ * a + c₀ = 0 := by
  let f : Polynomial R := Polynomial.X ^ 3 + Polynomial.C c₁ * Polynomial.X ^ 2 +
    Polynomial.C (c₂ * c₀) * Polynomial.X + Polynomial.C (c₃ * c₀ ^ 2)
  have hf : f.Monic := by unfold f; monicity <;> norm_num
  have h₂r := (residue_eq_zero_iff _).mpr h₂
  have h₃r := (residue_eq_zero_iff _).mpr h₃
  have h₁r := (residue_ne_zero_iff_isUnit _).mpr h₁
  have hroot : f.eval (-c₁) ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp [f, h₂r, h₃r]
    ring
  have hd : residue R (f.derivative.eval (-c₁)) = residue R c₁ ^ 2 := by
    simp [f, Polynomial.derivative_pow, Polynomial.derivative_mul, h₂r]
    simp only [map_ofNat]
    ring
  have hu : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval (-c₁))) := by
    change IsUnit (residue R (f.derivative.eval (-c₁)))
    rw [hd]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 h₁r)
  obtain ⟨u, he, hm⟩ := HenselianRing.is_henselian f hf (-c₁) hroot hu
  have hur : residue R u = -residue R c₁ := by
    have h := (residue_eq_zero_iff _).mpr hm
    simpa only [map_sub, map_neg, sub_eq_zero] using h
  have huu : IsUnit u := (residue_ne_zero_iff_isUnit _).mp (hur ▸ neg_ne_zero.mpr h₁r)
  obtain ⟨v, hv⟩ := huu.exists_right_inv
  have he' : u ^ 3 + c₁ * u ^ 2 + c₂ * c₀ * u + c₃ * c₀ ^ 2 = 0 := by
    simpa [Polynomial.IsRoot, f] using he
  have hh : 1 + c₁ * v + c₂ * c₀ * v ^ 2 + c₃ * c₀ ^ 2 * v ^ 3 = 0 := by
    calc
      _ = (u * v) ^ 3 + c₁ * (u * v) ^ 2 * v +
          c₂ * c₀ * (u * v) * v ^ 2 + c₃ * c₀ ^ 2 * v ^ 3 := by rw [hv]; ring
      _ = (u ^ 3 + c₁ * u ^ 2 + c₂ * c₀ * u + c₃ * c₀ ^ 2) * v ^ 3 := by ring
      _ = 0 := by rw [he', zero_mul]
  refine ⟨c₀ * v, ?_⟩
  linear_combination c₀ * hh

end FLT.Mazur
