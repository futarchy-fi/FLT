/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialCoefficientRing
public import FLT.Mazur.PrincipalRelationClosure
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Common coefficients for finite families on principal opens

Include the denominators and the numerators of every selected fraction in one
Noetherian coefficient subring. The resulting coefficient localizations map
injectively to the original principal opens and contain all selected elements.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) (r : ∀ i, MvPolynomial (Fin (n i)) R)
  {K : ι → Type w} [∀ i, Finite (K i)]

/-- Denominators and finitely many fractions descend to actual coefficient localizations. -/
theorem exists_localized_coefficients
    (x : ∀ i, K i → Localization.Away (r i))
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
          (∀ i, Function.Injective (d i)) ∧
          ∀ i k, x i k ∈ Set.range (d i) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i) := Fintype.ofFinite (K i)
  choose p m hm using fun i k ↦ IsLocalization.exists_mk'_eq
    (Submonoid.powers (r i)) (x i k)
  choose a ha using fun i k ↦ (m i k).property
  let T := ι ⊕ ((Σ i, K i) ⊕ (Σ i, ↥(seed i)))
  let _ : Fintype T := inferInstanceAs (Fintype
    (ι ⊕ ((Σ i, K i) ⊕ (Σ i, ↥(seed i)))))
  let v : T → Type := fun t ↦ match t with
    | .inl i => Fin (n i)
    | .inr (.inl ⟨i, _⟩) => Fin (n i)
    | .inr (.inr ⟨i, _⟩) => Fin (n i)
  let q : ∀ t, MvPolynomial (v t) R := fun t ↦ match t with
    | .inl i => r i
    | .inr (.inl ⟨i, k⟩) => p i k
    | .inr (.inr ⟨_, z⟩) => z.val
  obtain ⟨S, hS, hq⟩ := exists_coefficient_ring q
  choose q₀ hq₀ using hq
  let r₀ (i) := q₀ (.inl i)
  have hr (i) : MvPolynomial.map S.subtype (r₀ i) = r i := hq₀ (.inl i)
  let c (i) := MvPolynomial.map (σ := Fin (n i)) S.subtype
  have hM (i) : (Submonoid.powers (r₀ i)).map (c i) = Submonoid.powers (r i) := by
    rw [Submonoid.map_powers, hr]
  have hle (i) : Submonoid.powers (r₀ i) ≤ (Submonoid.powers (r i)).comap (c i) := by
    rw [← hM i]
    exact (Submonoid.powers (r₀ i)).le_comap_map
  let d (i) : Localization.Away (r₀ i) →+* Localization.Away (r i) :=
    IsLocalization.map _ (c i) (hle i)
  refine ⟨S, hS, fun i z hz ↦ ⟨q₀ (.inr (.inr ⟨i, ⟨z, hz⟩⟩)), hq₀ _⟩,
    r₀, hr, d, fun i ↦ IsLocalization.map_comp (hle i), ?_, ?_⟩
  · intro i
    let _ : IsLocalization ((Submonoid.powers (r₀ i)).map (c i))
        (Localization.Away (r i)) := by
      rw [hM i]
      infer_instance
    exact IsLocalization.map_injective_of_injective (Submonoid.powers (r₀ i))
      (Localization.Away (r₀ i)) (Localization.Away (r i))
      (coefficient_map_injective S (Fin (n i)))
  · intro i k
    refine ⟨IsLocalization.mk' (M := Submonoid.powers (r₀ i)) (Localization.Away (r₀ i))
      (q₀ (.inr (.inl ⟨i, k⟩))) ⟨r₀ i ^ a i k, ⟨a i k, rfl⟩⟩, ?_⟩
    change IsLocalization.map _ (c i) (hle i) _ = _
    rw [IsLocalization.map_mk']
    have hp : c i (q₀ (.inr (.inl ⟨i, k⟩))) = p i k := hq₀ _
    rw [hp]
    convert hm i k using 1
    apply congrArg (IsLocalization.mk' (Localization.Away (r i)) (p i k))
    apply Subtype.ext
    change c i (r₀ i ^ a i k) = (m i k).val
    rw [map_pow, hr]
    exact ha i k

end FLT.Mazur.FinitePolynomialCoefficients
