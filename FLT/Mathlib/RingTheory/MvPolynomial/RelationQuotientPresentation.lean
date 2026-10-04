/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # The presentation given by the original polynomial relation family -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R ι σ : Type*} [CommRing R]

/-- The quotient by a relation family has the presentation with exactly those variables
and exactly those relations. The original polynomial coordinates are retained. -/
def relationQuotientPresentation (g : ι → MvPolynomial σ R) :
    Algebra.Presentation R (MvPolynomial σ R ⧸ Ideal.span (Set.range g)) σ ι := by
  let I := Ideal.span (Set.range g)
  let f := Ideal.Quotient.mkₐ R I
  have he : aeval (fun i ↦ f (X i)) = f := by ext i; simp
  have hs : Function.Surjective (aeval (R := R) (fun i ↦ f (X i))) := by
    rw [he]
    exact Ideal.Quotient.mk_surjective
  exact {
    toGenerators := Algebra.Generators.ofSurjective (fun i ↦ f (X i)) hs
    relation := g
    span_range_relation_eq_ker := by
      change I = RingHom.ker (aeval (fun i ↦ f (X i))).toRingHom
      rw [he]
      exact Ideal.mk_ker.symm }

end MvPolynomial
