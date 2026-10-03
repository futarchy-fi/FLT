/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.DvrAdicTopology
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Continuity of the actual local Galois action

An automorphism preserves integral elements, so it preserves the valuation
subring and all valuation comparisons. The valuation neighborhood basis
then proves continuity; no invariant valuation or continuity is assumed.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Filter
open scoped Topology WithZero

variable (R S L : Type) [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Field L] [Algebra R L] [Algebra S L]
  [IsFractionRing S L] [IsIntegralClosure S R L]

omit [IsDomain S] [IsDiscreteValuationRing S] [IsFractionRing S L] in
/-- A local automorphism preserves the actual DVR image because it preserves integrality. -/
theorem adicGalois_mem_integers_iff (σ : L ≃ₐ[R] L) (x : L) :
    σ x ∈ Set.range (algebraMap S L) ↔ x ∈ Set.range (algebraMap S L) := by
  change (∃ s, algebraMap S L s = σ x) ↔ ∃ s, algebraMap S L s = x
  rw [← IsIntegralClosure.isIntegral_iff (R := R),
    ← IsIntegralClosure.isIntegral_iff (R := R)]
  exact isIntegral_algEquiv σ

/-- Automorphisms preserve valuation comparisons on the fraction field. -/
theorem adicGalois_valuation_isEquiv (σ : L ≃ₐ[R] L) :
    ((dvrPrime S).valuation L).IsEquiv
      (((dvrPrime S).valuation L).comap σ.toRingHom) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  have h := adicGalois_mem_integers_iff R S L σ x
  rw [dvrAdicValued_integers] at h
  exact h.symm

/-- The actual Galois automorphism is continuous for the constructed adic topology. -/
theorem adicGalois_continuous (σ : L ≃ₐ[R] L) :
    letI := dvrAdicValued S L
    Continuous σ := by
  let := dvrAdicValued S L
  apply continuous_of_continuousAt_zero σ.toRingHom
  simp only [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero L ℤᵐ⁰).tendsto_iff (Valued.hasBasis_nhds_zero L ℤᵐ⁰)]
  intro γ _
  obtain ⟨r, hr⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (.ofClass (Valued.v : Valuation L ℤᵐ⁰)) γ.val
  change Valued.v.restrict r = γ.val at hr
  have hr0 : r ≠ 0 := by
    intro h
    apply γ.ne_zero
    rw [← hr, h, map_zero]
  have hs0 : Valued.v.restrict (σ.symm r) ≠ 0 := by
    simpa using hr0
  refine ⟨Units.mk0 _ hs0, trivial, ?_⟩
  intro x hx
  change Valued.v.restrict (σ x) < γ.val
  rw [← hr, Valuation.restrict_lt_iff]
  have hx' : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (σ.symm r) :=
    Valued.v.restrict_lt_iff.mp hx
  have h := (Valuation.isEquiv_iff_val_lt_val.mp
    (adicGalois_valuation_isEquiv R S L σ)).mp hx'
  change (dvrPrime S).valuation L (σ x) <
    (dvrPrime S).valuation L (σ (σ.symm r)) at h
  rw [σ.apply_symm_apply] at h
  exact h

end LocalClassFieldTheory
