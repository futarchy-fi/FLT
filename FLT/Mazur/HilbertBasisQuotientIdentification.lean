/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisSchemeGluing

/-!
# Independence of the quotient presentation

An algebra identification preserving the ambient polynomial generators
identifies the actual ideals. The intrinsic opens and glued morphisms agree
under the induced identification of open subschemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

variable (I : Type u) (S : Type u) [CommRing S]
variable (J K : Ideal (MvPolynomial I S))

/-- Identifying quotient algebras with their ambient generators identifies their actual ideals. -/
theorem polynomialIdeal_eq_of_quotientEquiv
    (e : (MvPolynomial I S ⧸ J) ≃ₐ[S] (MvPolynomial I S ⧸ K))
    (he : ∀ i, e (quotientGenerator I S J i) = quotientGenerator I S K i) : J = K := by
  have h : e.toAlgHom.comp (Ideal.Quotient.mkₐ S J) = Ideal.Quotient.mkₐ S K := by
    apply MvPolynomial.algHom_ext
    exact he
  ext p
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  have hp := congrArg (fun f : MvPolynomial I S →ₐ[S] (MvPolynomial I S ⧸ K) ↦ f p) h
  change e (Ideal.Quotient.mk J p) = Ideal.Quotient.mk K p at hp
  rw [← hp]
  exact (map_eq_zero_iff e e.injective).symm

variable (R : Type u) [CommRing R] [Algebra R S] (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ K)]

/-- The intrinsic polynomial basis open is independent of a compatible quotient identification. -/
theorem polynomialBasisOpen_quotientEquiv
    (e : (MvPolynomial I S ⧸ J) ≃ₐ[S] (MvPolynomial I S ⧸ K))
    (he : ∀ i, e (quotientGenerator I S J i) = quotientGenerator I S K i) :
    polynomialBasisOpen R I d w S J = polynomialBasisOpen R I d w S K := by
  have h := polynomialIdeal_eq_of_quotientEquiv I S J K e he
  subst K
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual glued morphisms agree under the quotient-induced identification of basis schemes. -/
theorem intrinsicChartMorphism_quotientEquiv
    (e : (MvPolynomial I S ⧸ J) ≃ₐ[S] (MvPolynomial I S ⧸ K))
    (he : ∀ i, e (quotientGenerator I S J i) = quotientGenerator I S K i) :
    ((Spec (.of S)).isoOfEq
      (polynomialBasisOpen_quotientEquiv I S J K R d w e he)).hom ≫
      intrinsicChartMorphism R I d w S K = intrinsicChartMorphism R I d w S J := by
  have h := polynomialIdeal_eq_of_quotientEquiv I S J K e he
  subst K
  simp

end FLT.Mazur.HilbertChart
