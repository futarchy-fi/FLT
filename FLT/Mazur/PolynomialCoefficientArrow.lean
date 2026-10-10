/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialCoefficientRing

/-!
# Coefficient arrows from images of polynomial generators

A square on scalar rings and lifts of the variable images construct the
entire polynomial coefficient arrow. The target need not be a polynomial ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

variable {R : Type*} [CommRing R] (S : Subring R)
  {B₀ B : Type*} [CommRing B₀] [CommRing B] [Algebra S B₀] [Algebra R B]
  (d : B₀ →+* B)

/-- Descend a polynomial arrow by lifting generators, with full scalar compatibility. -/
theorem exists_polynomial_coefficient_arrow {σ : Type*}
    (hd : d.comp (algebraMap S B₀) = (algebraMap R B).comp S.subtype)
    (f : MvPolynomial σ R →ₐ[R] B)
    (hx : ∀ k, f (MvPolynomial.X k) ∈ Set.range d) :
    ∃ f₀ : MvPolynomial σ S →ₐ[S] B₀,
      f.toRingHom.comp (MvPolynomial.map S.subtype) = d.comp f₀.toRingHom := by
  choose x hx using hx
  refine ⟨MvPolynomial.aeval x, ?_⟩
  apply MvPolynomial.ringHom_ext
  · intro a
    change f (MvPolynomial.map S.subtype (MvPolynomial.C a)) =
      d (MvPolynomial.aeval x (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    change f (algebraMap R (MvPolynomial σ R) (S.subtype a)) = _
    rw [f.commutes]
    exact (RingHom.congr_fun hd a).symm
  · intro k
    change f (MvPolynomial.map S.subtype (MvPolynomial.X k)) =
      d (MvPolynomial.aeval x (MvPolynomial.X k))
    rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact (hx k).symm

end FLT.Mazur.FinitePolynomialCoefficients
