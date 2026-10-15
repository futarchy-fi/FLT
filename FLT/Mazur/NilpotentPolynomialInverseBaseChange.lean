/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentPolynomialInverse

/-!
# Nilpotent polynomial inverses after arbitrary coefficient extension

The same finite contraction solves the equation in every coefficient algebra,
including localizations and the actual initial chart itself.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentPolynomialInverse
variable {R S : Type*} [CommRing R] [CommRing S]
  (I : Ideal R) (hI : IsNilpotent I) (f : R →+* S)

include hI in
/-- The extended arithmetic ideal is nilpotent without a flatness hypothesis. -/
theorem mapIdeal_nilpotent : IsNilpotent (I.map f) := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, ?_⟩
  rw [← Ideal.map_pow, hN]
  exact Ideal.map_bot

variable (p : R[X]) (hp : p ∈ I.map C)

include hp in
/-- Every extended correction coefficient stays in the extended arithmetic ideal. -/
theorem mapPolynomial_mem : p.map f ∈ (I.map f).map C := by
  apply Ideal.mem_map_C_iff.mpr
  intro n
  rw [coeff_map]
  exact Ideal.mem_map_of_mem f (Ideal.mem_map_C_iff.mp hp n)

variable (a : S) (ha : IsUnit a) (b : S)

/-- The inverse incidence coordinate in an arbitrary coefficient algebra. -/
def extendedInverse : S :=
  inverse (I.map f) (p.map f) (mapPolynomial_mem I f p hp)
    (mapIdeal_nilpotent I hI f) a ha b

/-- The constructed extended inverse solves the full original coefficient equation. -/
theorem extendedInverse_equation :
    a * extendedInverse I hI f p hp a ha b +
      p.eval₂ f (extendedInverse I hI f p hp a ha b) = b := by
  simpa only [extendedInverse, eval_map] using inverse_equation (I.map f) (p.map f)
    (mapPolynomial_mem I f p hp) (mapIdeal_nilpotent I hI f) a ha b

include hp hI ha in
/-- Any two extended solutions coincide, with no additional residue constraint. -/
theorem extended_solution_unique {x y : S}
    (hx : a * x + p.eval₂ f x = b) (hy : a * y + p.eval₂ f y = b) : x = y := by
  apply solution_unique (I.map f) (p.map f) (mapPolynomial_mem I f p hp)
    (mapIdeal_nilpotent I hI f) a ha b
  · simpa only [eval_map] using hx
  · simpa only [eval_map] using hy

end FLT.Mazur.NilpotentPolynomialInverse
