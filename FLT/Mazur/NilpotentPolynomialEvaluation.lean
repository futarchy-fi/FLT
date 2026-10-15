/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentPolynomialInverseBaseChange
public import FLT.Mazur.NilpotentQuadraticRoot

/-!
# Nilpotent polynomial corrections in arbitrary coefficient algebras

Evaluation preserves the extended arithmetic ideal. This proves that the
denominators used for the full initial node comparisons remain units.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentPolynomialInverse
variable {R S : Type*} [CommRing R] [CommRing S]
  (I : Ideal R) (f : R →+* S) (p : R[X]) (hp : p ∈ I.map C)

include hp in
/-- Every polynomial value belongs to the extended coefficient ideal. -/
theorem eval₂_mem (z : S) : p.eval₂ f z ∈ I.map f := by
  classical
  rw [eval₂_eq_sum, Polynomial.sum]
  apply Submodule.sum_mem
  intro n _
  exact (I.map f).mul_mem_right _
    (Ideal.mem_map_of_mem f (Ideal.mem_map_C_iff.mp hp n))

include hp in
/-- A polynomial arithmetic correction is nilpotent at every incidence value. -/
theorem eval₂_nilpotent (hI : IsNilpotent I) (z : S) : IsNilpotent (p.eval₂ f z) :=
  NilpotentQuadraticRoot.element_nilpotent (I.map f) (mapIdeal_nilpotent I hI f)
    (eval₂_mem I f p hp z)

end FLT.Mazur.NilpotentPolynomialInverse
