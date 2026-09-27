/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Degree-one Frobenius comparison in a tower

Leaf H3 of `docs/CHEBOTAREV_PLAN.md`. The norm is written as `v.asIdeal.absNorm`,
and the inclusion of automorphism groups is `AlgEquiv.restrictScalarsHom ℚ`.
The fields are supplied as a tower with `L/F` and `L/ℚ` Galois. This applies
to every intermediate field of a finite Galois `L/ℚ`. Unramifiedness is not
needed to transport a given Frobenius congruence.
-/

@[expose] public section

open NumberField

namespace GaloisRepresentation.Chebotarev

/-- The rational prime associated to `q` has residue field of cardinality `q`. -/
theorem card_quotient_rationalPrime (q : ℕ) (hq : q.Prime) :
    Nat.card ((𝓞 ℚ) ⧸ hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) = q := by
  let e : (𝓞 ℚ) ⧸ hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal ≃+* ZMod q :=
    (Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv (by
      change Ideal.span {(q : ℤ)} =
        Ideal.map Rat.ringOfIntegersEquiv.toRingHom
          (Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(q : ℤ)}))
      exact (Ideal.map_comap_of_surjective Rat.ringOfIntegersEquiv.toRingHom
        Rat.ringOfIntegersEquiv.surjective _).symm)).trans
      (Int.quotientSpanNatEquivZMod q)
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

variable (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L]

/-- A prime of prime norm `q` lies above the rational prime `q`. -/
theorem under_eq_rationalPrime_of_absNorm_eq (v : Prime F) (q : ℕ) (hq : q.Prime)
    (hv : v.asIdeal.absNorm = q) :
    v.asIdeal.under (𝓞 ℚ) = hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
  have h := Ideal.span_singleton_absNorm (I := v.asIdeal) (hv ▸ hq)
  rw [hv] at h
  apply Ideal.comap_injective_of_surjective (algebraMap ℤ (𝓞 ℚ))
    (by
      rw [show algebraMap ℤ (𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm.toRingHom from
        Subsingleton.elim _ _]
      exact Rat.ringOfIntegersEquiv.symm.surjective)
  change (v.asIdeal.under (𝓞 ℚ)).under ℤ = _
  rw [Ideal.under_under, Ideal.under_def, ← h]
  ext x
  simp [Nat.Prime.toHeightOneSpectrumRingOfIntegersRat, RingEquiv.heightOneSpectrum,
    RingEquiv.heightOneSpectrumComap, Nat.Prime.toHeightOneSpectrumInt,
    Ideal.mem_comap, map_intCast]

variable [IsGalois F L] [IsGalois ℚ L]

/-- At a prime above one of norm `q`, relative Frobenius is rational Frobenius. -/
theorem isArithFrobAt_tower_degreeOne (v : Prime F) (q : ℕ) (hq : q.Prime)
    (hv : v.asIdeal.absNorm = q) (w : Prime L)
    (hw : w.asIdeal.under (𝓞 F) = v.asIdeal) (a : Gal(L/F))
    (ha : IsArithFrobAt (𝓞 F) a w.asIdeal) :
    IsArithFrobAt (𝓞 ℚ) (AlgEquiv.restrictScalarsHom ℚ a) w.asIdeal := by
  have hwq : w.asIdeal.under (𝓞 ℚ) = hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
    rw [← Ideal.under_under (B := 𝓞 F), hw]
    exact under_eq_rationalPrime_of_absNorm_eq F v q hq hv
  intro x
  have hx := ha x
  change a • x - x ^ Nat.card ((𝓞 F) ⧸ w.asIdeal.under (𝓞 F)) ∈ w.asIdeal at hx
  change a • x - x ^ Nat.card ((𝓞 ℚ) ⧸ w.asIdeal.under (𝓞 ℚ)) ∈ w.asIdeal
  rw [hwq, card_quotient_rationalPrime]
  rw [hw] at hx
  change a • x - x ^ v.asIdeal.absNorm ∈ w.asIdeal at hx
  rw [hv] at hx
  exact hx

/-- Degree-one tower comparison (leaf H3): the same prime witnesses rational Frobenius. -/
theorem hasFrob_tower_degreeOne (v : Prime F) (q : ℕ) (hq : q.Prime)
    (hv : v.asIdeal.absNorm = q) (a : Gal(L/F)) (ha : HasFrob F L v a) :
    HasFrob ℚ L hq.toHeightOneSpectrumRingOfIntegersRat
      (AlgEquiv.restrictScalarsHom ℚ a) := by
  obtain ⟨w, hw, ha⟩ := ha
  refine ⟨w, ?_, isArithFrobAt_tower_degreeOne F L v q hq hv w hw a ha⟩
  rw [← Ideal.under_under (B := 𝓞 F), hw]
  exact under_eq_rationalPrime_of_absNorm_eq F v q hq hv

end GaloisRepresentation.Chebotarev
