/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.FinitePrincipalIdealCover

/-! # Finite regular charts of a specified presentation, retaining relation counts -/

@[expose] public noncomputable section

namespace AlgHom

variable {k S A : Type*} [CommRing k] [CommRing S] [CommRing A]
  [Algebra k S] [Algebra k A] [IsNoetherianRing S]

/-- Regular relations at every prime give a finite cover of the actual presented algebra.
Each chart retains the original relation count and every original coordinate. -/
theorem exists_finite_regular_presentation_cover (f : S →ₐ[k] A)
    (hf : Function.Surjective f) (n : ℕ)
    (h : ∀ (P : Ideal S) [P.IsPrime], RingHom.ker f ≤ P →
      ∃ rs : List (Localization.AtPrime P), rs.length = n ∧
        Ideal.ofList rs = (RingHom.ker f).map (algebraMap S (Localization.AtPrime P)) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs) :
    ∃ (t : Finset (S ⧸ RingHom.ker f)) (a : t → S) (qs : t → List S),
      Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ ∧
      ∀ i, (qs i).length = n ∧ (∀ q ∈ qs i, f q = 0) ∧
        RingTheory.Sequence.IsRegular (Localization.Away (a i))
          ((qs i).map (algebraMap S (Localization.Away (a i)))) ∧
        ∃ e : (Localization.Away (a i) ⧸
            Ideal.ofList ((qs i).map (algebraMap S (Localization.Away (a i))))) ≃ₐ[k]
            Localization.Away (f (a i)),
          ∀ s : S, e (Ideal.Quotient.mk _ (algebraMap S _ s)) = algebraMap A _ (f s) := by
  let I := RingHom.ker f
  let P (a : S) := ∃ qs : List S, qs.length = n ∧ (∀ q ∈ qs, q ∈ I) ∧
    RingTheory.Sequence.IsRegular (Localization.Away a)
      (qs.map (algebraMap S (Localization.Away a))) ∧
    Ideal.ofList (qs.map (algebraMap S (Localization.Away a))) =
      I.map (algebraMap S (Localization.Away a))
  have hP (p : Ideal S) [p.IsPrime] (hp : I ≤ p) : ∃ a ∉ p, P a := by
    obtain ⟨rs, hlen, hgen, hreg⟩ := h p hp
    obtain ⟨a, qs, ha, hqs, hlen', hreg', hgen'⟩ :=
      RingTheory.Sequence.exists_away_regular_ideal_presentation p I rs hreg hgen
    exact ⟨a, ha, qs, hlen'.trans hlen, hqs, hreg', hgen'⟩
  obtain ⟨t, a, ha, _, hspan⟩ := I.exists_finite_quotient_principal_cover P hP
  choose qs hlen hqs hreg hgen using ha
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have hspanA : Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ := by
    have hh := congrArg (Ideal.map e.toRingHom) hspan
    rw [Ideal.map_span, ← Set.range_comp, Ideal.map_top] at hh
    exact hh
  refine ⟨t, a, qs, hspanA, fun i ↦ ⟨hlen i, hqs i, hreg i, ?_⟩⟩
  have he : (Submonoid.powers (Ideal.Quotient.mk I (a i))).map e.toMonoidHom =
      Submonoid.powers (f (a i)) := by rw [Submonoid.map_powers]; rfl
  let e' := IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (Ideal.Quotient.mk I (a i))) (Localization.Away (f (a i))) e he
  let eqv := ((I.regularPresentationAwayEquiv (a i) (qs i) (hgen i)).restrictScalars k).trans e'
  refine ⟨eqv, fun s ↦ ?_⟩
  change e' (I.regularPresentationAwayEquiv (a i) (qs i) (hgen i)
    (algebraMap S _ s)) = _
  rw [Ideal.regularPresentationAwayEquiv_algebraMap,
    IsScalarTower.algebraMap_apply S (S ⧸ I)]
  exact IsLocalization.algEquivOfAlgEquiv_eq he _

end AlgHom
