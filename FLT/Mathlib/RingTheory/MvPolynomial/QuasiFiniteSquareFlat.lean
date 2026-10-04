/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.NoetherianQuasiFiniteSquareFlat
public import FLT.Mathlib.RingTheory.MvPolynomial.NoetherianQuasiFiniteStage

/-! # Quasi-finite square presentations over an arbitrary base are flat -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A quasi-finite square relation quotient is flat over any coefficient ring. We descend
quasi-finiteness to a Noetherian model, prove that model flat, and reconstruct by base change. -/
theorem flat_square_quotient_of_quasiFinite_arbitraryBase
    (f : Fin n → MvPolynomial (Fin n) R)
    [Algebra.QuasiFinite R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))] :
    Module.Flat R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) := by
  obtain ⟨S, _, hN, g, hg, hQ⟩ := exists_noetherian_quasiFinite_stage f
  have : IsNoetherianRing S := hN
  have : Algebra.QuasiFinite S (MvPolynomial (Fin n) S ⧸ Ideal.span (Set.range g)) := hQ
  have := flat_square_range_quotient_of_quasiFinite g
  have he : Ideal.span (Set.range fun i ↦ map (algebraMap S R) (g i)) =
      Ideal.span (Set.range f) := congrArg Ideal.span (congrArg Set.range (funext hg))
  exact Module.Flat.of_linearEquiv ((relationBaseChangeEquiv (S := R) g).trans
    (Ideal.quotientEquivAlgOfEq R he)).symm.toLinearEquiv

end MvPolynomial
