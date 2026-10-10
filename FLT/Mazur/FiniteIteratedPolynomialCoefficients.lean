/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocalizedPolynomialCoefficients
public import FLT.Mazur.PrincipalCoefficientTransport

/-!
# Common coefficients for finite families of iterated principal opens

At each ambient vertex, allow finitely many second denominators, each an
arbitrary fraction in its first principal localization. All selected outer
fractions and first-level data descend through one Noetherian coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z t

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {J : ι → Type w} [∀ i, Finite (J i)]
  (s : ∀ i, J i → Localization.Away (r i))
  {K : ι → Type z} [∀ i, Finite (K i)]
  {L : ∀ i, J i → Type t} [∀ i j, Finite (L i j)]

/-- One coefficient ring contains all first and second localization data simultaneously. -/
theorem exists_iterated_coefficients
    (x : ∀ i, K i → Localization.Away (r i))
    (y : ∀ i j, L i j → Localization.Away (s i j))
    (seed : ∀ i, Finset (MvPolynomial (Fin (n i)) R)) :
    ∃ S : Subring R, IsNoetherianRing S ∧
      (∀ i, (seed i : Set (MvPolynomial (Fin (n i)) R)) ⊆
        Set.range (MvPolynomial.map S.subtype)) ∧
      ∃ r₀ : ∀ i, MvPolynomial (Fin (n i)) S,
        (∀ i, MvPolynomial.map S.subtype (r₀ i) = r i) ∧
        ∃ d : ∀ i, Localization.Away (r₀ i) →+* Localization.Away (r i),
          (∀ i, (d i).comp
            (algebraMap (MvPolynomial (Fin (n i)) S) (Localization.Away (r₀ i))) =
            (algebraMap (MvPolynomial (Fin (n i)) R) (Localization.Away (r i))).comp
              (MvPolynomial.map S.subtype)) ∧
          (∀ i, Function.Injective (d i)) ∧ (∀ i k, x i k ∈ Set.range (d i)) ∧
          ∃ s₀ : ∀ i, J i → Localization.Away (r₀ i),
            (∀ i j, d i (s₀ i j) = s i j) ∧
            ∃ e : ∀ i j, Localization.Away (s₀ i j) →+* Localization.Away (s i j),
              (∀ i j, (e i j).comp
                (algebraMap (Localization.Away (r₀ i)) (Localization.Away (s₀ i j))) =
                (algebraMap (Localization.Away (r i)) (Localization.Away (s i j))).comp
                  (d i)) ∧
              (∀ i j, Function.Injective (e i j)) ∧
              ∀ i j k, y i j k ∈ Set.range (e i j) := by
  classical
  let _ (i) := Fintype.ofFinite (J i)
  let _ (i) := Fintype.ofFinite (K i)
  let _ (i j) := Fintype.ofFinite (L i j)
  choose p m hm using fun i j k ↦ IsLocalization.exists_mk'_eq
    (Submonoid.powers (s i j)) (y i j k)
  let T (i) := K i ⊕ (J i ⊕ (Σ j, L i j))
  let _ (i) : Fintype (T i) :=
    inferInstanceAs (Fintype (K i ⊕ (J i ⊕ (Σ j, L i j))))
  let z : ∀ i, T i → Localization.Away (r i) := fun i a ↦ match a with
    | .inl k => x i k
    | .inr (.inl j) => s i j
    | .inr (.inr ⟨j, k⟩) => p i j k
  obtain ⟨S, hS, hseed, r₀, hr, d, hd, hinj, hz⟩ :=
    exists_localized_coefficients n r z seed
  choose z₀ hz₀ using hz
  let s₀ (i) (j : J i) := z₀ i (.inr (.inl j))
  have hs (i j) : d i (s₀ i j) = s i j := hz₀ i (.inr (.inl j))
  let e (i j) :=
    NoetherianRelationContraction.principalTransport (d i) (s₀ i j) (s i j) (hs i j)
  refine ⟨S, hS, hseed, r₀, hr, d, hd, hinj,
    fun i k ↦ ⟨z₀ i (.inl k), hz₀ i (.inl k)⟩, s₀, hs, e,
    fun i j ↦ NoetherianRelationContraction.principalTransport_comp _ _ _ _,
    fun i j ↦ NoetherianRelationContraction.principalTransport_injective _ _ _ _ (hinj i),
    fun i j k ↦ ?_⟩
  rw [← hm i j k]
  exact NoetherianRelationContraction.principalTransport_mk'_mem_range _ _ _ _ _ _
    ⟨z₀ i (.inr (.inr ⟨j, k⟩)), hz₀ i (.inr (.inr ⟨j, k⟩))⟩

end FLT.Mazur.FinitePolynomialCoefficients
