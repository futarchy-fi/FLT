/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteOccurrenceLocalizedCoefficients
public import FLT.Mazur.PrincipalCoefficientTransport

/-!
# Shared coefficients for occurrence-specific double opens

Every first occurrence can have several second denominators. All denominators,
selected fractions and ambient seeds descend together. The polynomial
coefficient map depends only on the ambient chart, not on the occurrence.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z t e

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) {O : ι → Type w} [∀ i, Finite (O i)]
  (r : ∀ i, O i → MvPolynomial (Fin (n i)) R)
  {J : ∀ i, O i → Type z} [∀ i o, Finite (J i o)]
  (s : ∀ i o, J i o → Localization.Away (r i o))
  {K : ∀ i, O i → Type t} [∀ i o, Finite (K i o)]
  {L : ∀ i o, J i o → Type e} [∀ i o j, Finite (L i o j)]

/-- All occurrence-specific first and second localization data share one coefficient ring. -/
theorem exists_occurrence_iterated_coefficients
    (x : ∀ i o, K i o → Localization.Away (r i o))
    (y : ∀ i o j, L i o j → Localization.Away (s i o j))
    (seed : ∀ i, Finset (MvPolynomial (Fin (n i)) R)) :
    ∃ S : Subring R, IsNoetherianRing S ∧
      (∀ i, (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆
        Set.range (MvPolynomial.map S.subtype)) ∧
      ∃ r₀ : ∀ i, O i → MvPolynomial (Fin (n i)) S,
        (∀ i o, MvPolynomial.map S.subtype (r₀ i o) = r i o) ∧
        ∃ d : ∀ i o, Localization.Away (r₀ i o) →+* Localization.Away (r i o),
          (∀ i o, (d i o).comp
            (algebraMap (MvPolynomial (Fin (n i)) S) (Localization.Away (r₀ i o))) =
            (algebraMap (MvPolynomial (Fin (n i)) R) (Localization.Away (r i o))).comp
              (MvPolynomial.map S.subtype)) ∧
          (∀ i o, Function.Injective (d i o)) ∧ (∀ i o k, x i o k ∈ Set.range (d i o)) ∧
          ∃ s₀ : ∀ i o, J i o → Localization.Away (r₀ i o),
            (∀ i o j, d i o (s₀ i o j) = s i o j) ∧
            ∃ e : ∀ i o j, Localization.Away (s₀ i o j) →+* Localization.Away (s i o j),
              (∀ i o j, (e i o j).comp
                (algebraMap (Localization.Away (r₀ i o)) (Localization.Away (s₀ i o j))) =
                (algebraMap (Localization.Away (r i o)) (Localization.Away (s i o j))).comp
                  (d i o)) ∧
              (∀ i o j, Function.Injective (e i o j)) ∧
              ∀ i o j k, y i o j k ∈ Set.range (e i o j) := by
  classical
  let _ (i o) := Fintype.ofFinite (J i o)
  let _ (i o) := Fintype.ofFinite (K i o)
  let _ (i o j) := Fintype.ofFinite (L i o j)
  choose p m hm using fun i o j k ↦ IsLocalization.exists_mk'_eq
    (Submonoid.powers (s i o j)) (y i o j k)
  let T (i o) := K i o ⊕ (J i o ⊕ (Σ j, L i o j))
  let _ (i o) : Fintype (T i o) :=
    inferInstanceAs (Fintype (K i o ⊕ (J i o ⊕ (Σ j, L i o j))))
  let z : ∀ i o, T i o → Localization.Away (r i o) := fun i o a ↦ match a with
    | .inl k => x i o k
    | .inr (.inl j) => s i o j
    | .inr (.inr ⟨j, k⟩) => p i o j k
  obtain ⟨S, hS, hseed, r₀, hr, d, hd, hinj, hz⟩ :=
    exists_occurrence_localized_coefficients n r z seed
  choose z₀ hz₀ using hz
  let s₀ (i o) (j : J i o) := z₀ i o (.inr (.inl j))
  have hs (i o j) : d i o (s₀ i o j) = s i o j := hz₀ i o (.inr (.inl j))
  let e (i o j) := NoetherianRelationContraction.principalTransport
    (d i o) (s₀ i o j) (s i o j) (hs i o j)
  refine ⟨S, hS, hseed, r₀, hr, d, hd, hinj,
    fun i o k ↦ ⟨z₀ i o (.inl k), hz₀ i o (.inl k)⟩, s₀, hs, e,
    fun i o j ↦ NoetherianRelationContraction.principalTransport_comp _ _ _ _,
    fun i o j ↦ NoetherianRelationContraction.principalTransport_injective _ _ _ _ (hinj i o),
    fun i o j k ↦ ?_⟩
  rw [← hm i o j k]
  exact NoetherianRelationContraction.principalTransport_mk'_mem_range _ _ _ _ _ _
    ⟨z₀ i o (.inr (.inr ⟨j, k⟩)), hz₀ i o (.inr (.inr ⟨j, k⟩))⟩

end FLT.Mazur.FinitePolynomialCoefficients
