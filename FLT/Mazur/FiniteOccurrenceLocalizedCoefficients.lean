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
# Common coefficients for occurrence-specific principal opens

Allow several first denominators on each ambient chart. Every chart uses the
same coefficient subring, including charts with no occurrences. Ambient seeds
are retained without duplicating ambient ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) {O : ι → Type w} [∀ i, Finite (O i)]
  (r : ∀ i, O i → MvPolynomial (Fin (n i)) R)
  {K : ∀ i, O i → Type z} [∀ i o, Finite (K i o)]

/-- Denominators and finitely many fractions descend to actual coefficient localizations. -/
theorem exists_occurrence_localized_coefficients
    (x : ∀ i o, K i o → Localization.Away (r i o))
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
          (∀ i o, Function.Injective (d i o)) ∧
          ∀ i o k, x i o k ∈ Set.range (d i o) := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i) := Fintype.ofFinite (O i)
  let _ (i o) := Fintype.ofFinite (K i o)
  choose p m hm using fun i o k ↦ IsLocalization.exists_mk'_eq
    (Submonoid.powers (r i o)) (x i o k)
  choose a ha using fun i o k ↦ (m i o k).property
  let T := (Σ i, O i) ⊕ ((Σ i, Σ o, K i o) ⊕ (Σ i, ↥(seed i)))
  let _ : Fintype T := inferInstanceAs (Fintype
    ((Σ i, O i) ⊕ ((Σ i, Σ o, K i o) ⊕ (Σ i, ↥(seed i)))))
  let v : T → Type := fun t ↦ match t with
    | .inl ⟨i, _⟩ => Fin (n i)
    | .inr (.inl ⟨i, _, _⟩) => Fin (n i)
    | .inr (.inr ⟨i, _⟩) => Fin (n i)
  let q : ∀ t, MvPolynomial (v t) R := fun t ↦ match t with
    | .inl ⟨i, o⟩ => r i o
    | .inr (.inl ⟨i, o, k⟩) => p i o k
    | .inr (.inr ⟨_, z⟩) => z.val
  obtain ⟨S, hS, hq⟩ := exists_coefficient_ring q
  choose q₀ hq₀ using hq
  let r₀ (i o) := q₀ (.inl ⟨i, o⟩)
  have hr (i o) : MvPolynomial.map S.subtype (r₀ i o) = r i o := hq₀ (.inl ⟨i, o⟩)
  let c (i) := MvPolynomial.map (σ := Fin (n i)) S.subtype
  have hM (i o) : (Submonoid.powers (r₀ i o)).map (c i) = Submonoid.powers (r i o) := by
    rw [Submonoid.map_powers, hr]
  have hle (i o) : Submonoid.powers (r₀ i o) ≤ (Submonoid.powers (r i o)).comap (c i) := by
    rw [← hM i o]
    exact (Submonoid.powers (r₀ i o)).le_comap_map
  let d (i o) : Localization.Away (r₀ i o) →+* Localization.Away (r i o) :=
    IsLocalization.map _ (c i) (hle i o)
  refine ⟨S, hS, fun i z hz ↦ ⟨q₀ (.inr (.inr ⟨i, ⟨z, hz⟩⟩)), hq₀ _⟩,
    r₀, hr, d, fun i o ↦ IsLocalization.map_comp (hle i o), ?_, ?_⟩
  · intro i o
    let _ : IsLocalization ((Submonoid.powers (r₀ i o)).map (c i))
        (Localization.Away (r i o)) := by
      rw [hM i o]
      infer_instance
    exact IsLocalization.map_injective_of_injective (Submonoid.powers (r₀ i o))
      (Localization.Away (r₀ i o)) (Localization.Away (r i o))
      (coefficient_map_injective S (Fin (n i)))
  · intro i o k
    refine ⟨IsLocalization.mk' (M := Submonoid.powers (r₀ i o)) (Localization.Away (r₀ i o))
      (q₀ (.inr (.inl ⟨i, o, k⟩))) ⟨r₀ i o ^ a i o k, ⟨a i o k, rfl⟩⟩, ?_⟩
    change IsLocalization.map _ (c i) (hle i o) _ = _
    rw [IsLocalization.map_mk']
    have hp : c i (q₀ (.inr (.inl ⟨i, o, k⟩))) = p i o k := hq₀ _
    rw [hp]
    convert hm i o k using 1
    apply congrArg (IsLocalization.mk' (Localization.Away (r i o)) (p i o k))
    apply Subtype.ext
    change c i (r₀ i o ^ a i o k) = (m i o k).val
    rw [map_pow, hr]
    exact ha i o k

end FLT.Mazur.FinitePolynomialCoefficients
