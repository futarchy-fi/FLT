/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteOccurrenceIteratedCoefficients
public import FLT.Mazur.PolynomialCoefficientArrow

/-!
# Shared coefficient squares for occurrence-indexed arrows

Polynomial arrows into every first and second occurrence descend together.
Arbitrary inverse representatives and additional equations are included as
fraction data in the same coefficient ring, without duplicating ambient charts.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w z t e h q

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  (n : ι → ℕ) {O : ι → Type q} [∀ i, Finite (O i)]
  (r : ∀ i, O i → MvPolynomial (Fin (n i)) R)
  {J : ∀ i, O i → Type w} [∀ i o, Finite (J i o)]
  (s : ∀ i o, J i o → Localization.Away (r i o))
  {K : ∀ i, O i → Type z} [∀ i o, Finite (K i o)]
  {L : ∀ i o, J i o → Type t} [∀ i o j, Finite (L i o j)]
  {E : ∀ (_ : ι) j, O j → Type e} [∀ i j o, Finite (E i j o)]
  {H : ∀ (_ : ι) j o, J j o → Type h} [∀ i j o k, Finite (H i j o k)]

/-- Descend both levels of a finite diagram through one coefficient ring. -/
theorem exists_occurrence_diagram_coefficients
    (f : ∀ i j o, E i j o → MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (r j o))
    (g : ∀ i j o k, H i j o k →
      MvPolynomial (Fin (n i)) R →ₐ[R] Localization.Away (s j o k))
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
              (∀ i o j k, y i o j k ∈ Set.range (e i o j)) ∧
              (∃ f₀ : ∀ i j o, E i j o →
                MvPolynomial (Fin (n i)) S →ₐ[S] Localization.Away (r₀ j o),
                ∀ i j o a, (f i j o a).toRingHom.comp (MvPolynomial.map S.subtype) =
                  (d j o).comp (f₀ i j o a).toRingHom) ∧
              ∃ g₀ : ∀ i j o k, H i j o k →
                MvPolynomial (Fin (n i)) S →ₐ[S] Localization.Away (s₀ j o k),
                ∀ i j o k a, (g i j o k a).toRingHom.comp (MvPolynomial.map S.subtype) =
                  (e j o k).comp (g₀ i j o k a).toRingHom := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (i o) := Fintype.ofFinite (K i o)
  let _ (i o j) := Fintype.ofFinite (L i o j)
  let _ (i j o) := Fintype.ofFinite (E i j o)
  let _ (i j o k) := Fintype.ofFinite (H i j o k)
  let T (j o) := (Σ i, E i j o × Fin (n i)) ⊕ K j o
  let U (j o) (k : J j o) := (Σ i, H i j o k × Fin (n i)) ⊕ L j o k
  let _ (j o) : Fintype (T j o) :=
    inferInstanceAs (Fintype ((Σ i, E i j o × Fin (n i)) ⊕ K j o))
  let _ (j o k) : Fintype (U j o k) :=
    inferInstanceAs (Fintype ((Σ i, H i j o k × Fin (n i)) ⊕ L j o k))
  let x' : ∀ j o, T j o → Localization.Away (r j o) := fun j o a ↦ match a with
    | .inl ⟨i, a, k⟩ => f i j o a (MvPolynomial.X k)
    | .inr k => x j o k
  let y' : ∀ j o k, U j o k → Localization.Away (s j o k) := fun j o k a ↦ match a with
    | .inl ⟨i, a, l⟩ => g i j o k a (MvPolynomial.X l)
    | .inr l => y j o k l
  obtain ⟨S, hS, hseed, r₀, hr, d, hd, hinj, hx, s₀, hs, e, he, heinj, hy⟩ :=
    exists_occurrence_iterated_coefficients n r s x' y' seed
  have hdS (j o) : (d j o).comp (algebraMap S (Localization.Away (r₀ j o))) =
      (algebraMap R (Localization.Away (r j o))).comp S.subtype := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply S (MvPolynomial (Fin (n j)) S),
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin (n j)) R)]
    have h := RingHom.congr_fun (hd j o) (MvPolynomial.C a)
    simpa only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.algebraMap_eq] using h
  have heS (j o k) : (e j o k).comp (algebraMap S (Localization.Away (s₀ j o k))) =
      (algebraMap R (Localization.Away (s j o k))).comp S.subtype := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply S (Localization.Away (r₀ j o))]
    have h := RingHom.congr_fun (he j o k)
      (algebraMap S (Localization.Away (r₀ j o)) a)
    simp only [RingHom.comp_apply] at h
    rw [h]
    have h' := RingHom.congr_fun (hdS j o) a
    simp only [RingHom.comp_apply] at h'
    rw [h']
    exact (IsScalarTower.algebraMap_apply R (Localization.Away (r j o)) _ _).symm
  choose f₀ hf₀ using fun i j o a ↦ exists_polynomial_coefficient_arrow S (d j o)
    (hdS j o) (f i j o a) (fun k ↦ hx j o (.inl ⟨i, a, k⟩))
  choose g₀ hg₀ using fun i j o k a ↦ exists_polynomial_coefficient_arrow S (e j o k)
    (heS j o k) (g i j o k a) (fun l ↦ hy j o k (.inl ⟨i, a, l⟩))
  exact ⟨S, hS, hseed, r₀, hr, d, hd, hinj, fun i o k ↦ hx i o (.inr k), s₀, hs,
    e, he, heinj, fun i o j k ↦ hy i o j (.inr k), ⟨f₀, hf₀⟩, g₀, hg₀⟩

end FLT.Mazur.FinitePolynomialCoefficients
