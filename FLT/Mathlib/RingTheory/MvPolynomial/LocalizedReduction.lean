/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # Reduction of localized polynomial rings -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Coefficient reduction agrees with the inverse of the polynomial quotient equivalence. -/
@[simp] theorem quotientEquivQuotientMvPolynomial_symm_mk (I : Ideal R)
    (f : MvPolynomial σ R) :
    (quotientEquivQuotientMvPolynomial (σ := σ) I).symm
      (Ideal.Quotient.mk (I.map C) f) = map (Ideal.Quotient.mk I) f := by
  rw [map_eq_eval₂Hom_C_comp]
  rfl

/-- The coefficient action factors through the reduced polynomial source. -/
instance localizedReductionScalarTower (I : Ideal R) (M : Submonoid (MvPolynomial σ R)) :
    IsScalarTower R (MvPolynomial σ R ⧸ I.map C)
      (Localization M ⧸ (I.map (C (σ := σ))).map
        (algebraMap (MvPolynomial σ R) (Localization M))) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change Ideal.Quotient.mk _ (algebraMap R (Localization M) r) =
        Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ R) (Localization M) (C r))
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R) (Localization M)]
      rfl
/-- The quotient of a polynomial localization localizes the quotient polynomial ring. -/
instance localizedReductionIsLocalization (I : Ideal R) (M : Submonoid (MvPolynomial σ R)) :
    IsLocalization (M.map (Ideal.Quotient.mk (I.map C)))
      (Localization M ⧸ (I.map (C (σ := σ))).map
        (algebraMap (MvPolynomial σ R) (Localization M))) :=
    IsLocalization.of_surjective M (Localization M)
      (Ideal.Quotient.mk (I.map C)) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk ((I.map C).map (algebraMap _ (Localization M))))
      Ideal.Quotient.mk_surjective rfl (by simp)

/-- Reducing denominators before or after the polynomial quotient comparison agrees. -/
theorem localizedReduction_denominators (I : Ideal R) (M : Submonoid (MvPolynomial σ R)) :
    (M.map (Ideal.Quotient.mk (I.map C))).map
        (quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom =
      M.map (map (Ideal.Quotient.mk I)) := by
  ext y
  simp only [Submonoid.mem_map]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (quotientEquivQuotientMvPolynomial_symm_mk I x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Ideal.Quotient.mk _ x, ⟨x, hx, rfl⟩,
      quotientEquivQuotientMvPolynomial_symm_mk I x⟩

/-- Reduction commutes with localization of a polynomial ring. The denominators
on the right are the reductions of the original denominators. -/
def localizedReductionEquiv (I : Ideal R) (M : Submonoid (MvPolynomial σ R)) :
    (Localization M ⧸ (I.map (C (σ := σ))).map
      (algebraMap (MvPolynomial σ R) (Localization M))) ≃ₐ[R]
      Localization (M.map (map (Ideal.Quotient.mk I))) := by
  let := localizedReductionScalarTower I M
  let := localizedReductionIsLocalization I M
  exact IsLocalization.algEquivOfAlgEquiv _ _
    (quotientEquivQuotientMvPolynomial I).symm (localizedReduction_denominators I M)

/-- The localized reduction comparison sends each polynomial to its coefficient reduction. -/
theorem localizedReductionEquiv_mk (I : Ideal R)
    (M : Submonoid (MvPolynomial σ R)) (f : MvPolynomial σ R) :
    localizedReductionEquiv I M
      (Ideal.Quotient.mk _ (algebraMap _ (Localization M) f)) =
    algebraMap _ (Localization (M.map (map (Ideal.Quotient.mk I))))
      (map (Ideal.Quotient.mk I) f) := by
  let := localizedReductionScalarTower I M
  let := localizedReductionIsLocalization I M
  exact (IsLocalization.algEquivOfAlgEquiv_eq
    (S := Localization M ⧸ (I.map C).map (algebraMap (MvPolynomial σ R) (Localization M)))
    (Q := Localization (M.map (map (Ideal.Quotient.mk I))))
    (localizedReduction_denominators I M) (Ideal.Quotient.mk _ f)).trans
      (congrArg _ (quotientEquivQuotientMvPolynomial_symm_mk I f))

/-- Reduction modulo a single base parameter commutes with polynomial localization. -/
def localizedModPrincipalEquiv (p : R) (M : Submonoid (MvPolynomial σ R)) :
    (Localization M ⧸ Ideal.span {algebraMap R (Localization M) p}) ≃ₐ[R]
      Localization (M.map (map (Ideal.Quotient.mk (Ideal.span {p})))) :=
  (Ideal.quotientEquivAlgOfEq R (by
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rfl)).trans (localizedReductionEquiv (Ideal.span {p}) M)

/-- The principal reduction comparison agrees with coefficient reduction on polynomials. -/
theorem localizedModPrincipalEquiv_mk (p : R)
    (M : Submonoid (MvPolynomial σ R)) (f : MvPolynomial σ R) :
    localizedModPrincipalEquiv p M
      (Ideal.Quotient.mk _ (algebraMap _ (Localization M) f)) =
    algebraMap _ (Localization (M.map (map (Ideal.Quotient.mk (Ideal.span {p})))))
      (map (Ideal.Quotient.mk (Ideal.span {p})) f) :=
  localizedReductionEquiv_mk (Ideal.span {p}) M f

end MvPolynomial
