/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.QuotientAwayPresentation
public import FLT.Mathlib.RingTheory.Regular.PrincipalIdealPresentation

/-! # A finite principal cover for locally regular Noetherian ideal presentations -/

@[expose] public noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- A principal neighbourhood at every prime of a quotient has a finite subcover.
The witnesses retain lifts of the denominators to the original ring. -/
theorem exists_finite_quotient_principal_cover (I : Ideal R) (P : R → Prop)
    (h : ∀ (p : Ideal R) [p.IsPrime], I ≤ p → ∃ a ∉ p, P a) :
    ∃ (t : Finset (R ⧸ I)) (a : t → R),
      (∀ i, P (a i)) ∧
      (∀ i, Ideal.Quotient.mk I (a i) = i.val) ∧
      Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk I (a i)) = ⊤ := by
  classical
  let s : Set (R ⧸ I) := Ideal.Quotient.mk I '' {a | P a}
  have hs : Ideal.span s = ⊤ := by
    by_contra hn
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) hn
    let p := q.comap (Ideal.Quotient.mk I)
    have : q.IsMaximal := hq
    have : p.IsPrime := inferInstance
    have hIp : I ≤ p := by
      intro x hx
      change Ideal.Quotient.mk I x ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q.zero_mem
    obtain ⟨a, ha, hPa⟩ := h p hIp
    exact ha (hle (Ideal.subset_span ⟨a, hPa, rfl⟩))
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  have hex (i : t) : ∃ a : R, P a ∧ Ideal.Quotient.mk I a = i.val := ht i.property
  choose a ha heq using hex
  refine ⟨t, a, ha, heq, ?_⟩
  have hrange : Set.range (fun i ↦ Ideal.Quotient.mk I (a i)) = (t : Set (R ⧸ I)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change Ideal.Quotient.mk I (a i) ∈ (t : Set (R ⧸ I))
      rw [heq]
      exact i.property
    · intro hx
      exact ⟨⟨x, hx⟩, heq ⟨x, hx⟩⟩
  rwa [hrange]

end Ideal

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Regular local presentations of a Noetherian ideal give finitely many principal
regular presentations, with defining elements generating one in the quotient. -/
theorem exists_finite_principal_regular_ideal_cover (I : Ideal R)
    (h : ∀ (p : Ideal R) [p.IsPrime], I ≤ p →
      ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
        Ideal.ofList rs = I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ (t : Finset (R ⧸ I)) (a : t → R) (qs : t → List R),
      Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk I (a i)) = ⊤ ∧
      ∀ i, (∀ q ∈ qs i, q ∈ I) ∧
        IsRegular (Localization.Away (a i))
          ((qs i).map (algebraMap R (Localization.Away (a i)))) ∧
        Ideal.ofList ((qs i).map (algebraMap R (Localization.Away (a i)))) =
          I.map (algebraMap R (Localization.Away (a i))) := by
  let P (a : R) := ∃ qs : List R, (∀ q ∈ qs, q ∈ I) ∧
    IsRegular (Localization.Away a) (qs.map (algebraMap R (Localization.Away a))) ∧
      Ideal.ofList (qs.map (algebraMap R (Localization.Away a))) =
        I.map (algebraMap R (Localization.Away a))
  have hP (p : Ideal R) [p.IsPrime] (hIp : I ≤ p) : ∃ a ∉ p, P a := by
    obtain ⟨rs, hreg, hgen⟩ := h p hIp
    obtain ⟨a, qs, ha, hqs, _, hreg, hgen⟩ :=
      exists_away_regular_ideal_presentation p I rs hreg hgen
    exact ⟨a, ha, qs, hqs, hreg, hgen⟩
  obtain ⟨t, a, ha, _, hspan⟩ := I.exists_finite_quotient_principal_cover P hP
  choose qs hqs hreg hgen using ha
  exact ⟨t, a, qs, hspan, fun i ↦ ⟨hqs i, hreg i, hgen i⟩⟩

/-- The finite chart presentations identify the actual principal localizations of the
quotient and preserve all original coordinates. -/
theorem exists_finite_principal_regular_quotient_cover (I : Ideal R)
    (h : ∀ (p : Ideal R) [p.IsPrime], I ≤ p →
      ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
        Ideal.ofList rs = I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ (t : Finset (R ⧸ I)) (a : t → R) (qs : t → List R),
      Ideal.span (Set.range fun i ↦ Ideal.Quotient.mk I (a i)) = ⊤ ∧
      ∀ i, IsRegular (Localization.Away (a i))
          ((qs i).map (algebraMap R (Localization.Away (a i)))) ∧
        ∃ e : (Localization.Away (a i) ⧸
            Ideal.ofList ((qs i).map (algebraMap R (Localization.Away (a i))))) ≃ₐ[R]
            Localization.Away (Ideal.Quotient.mk I (a i)),
          ∀ r : R, e (algebraMap R _ r) = algebraMap R _ r := by
  obtain ⟨t, a, qs, hspan, hqs⟩ := exists_finite_principal_regular_ideal_cover I h
  refine ⟨t, a, qs, hspan, fun i ↦ ?_⟩
  exact ⟨(hqs i).2.1, I.regularPresentationAwayEquiv (a i) (qs i) (hqs i).2.2,
    fun r ↦ (I.regularPresentationAwayEquiv (a i) (qs i) (hqs i).2.2).commutes r⟩

end RingTheory.Sequence
