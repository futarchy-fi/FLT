/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Domain neighborhoods of Noetherian local domains

The kernel of localization is finitely generated. A single denominator kills
all of its generators, so a principal neighborhood embeds in the local ring.
If that local ring is a domain, this neighborhood is a domain as well.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve

/-- A domain prime localization of a Noetherian ring has a domain principal neighborhood. -/
theorem exists_domain_away_of_isDomain_atPrime
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)] :
    ∃ r : R, r ∉ p ∧ IsDomain (Localization.Away r) := by
  classical
  let A := Localization.AtPrime p
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (RingHom.ker (algebraMap R A))
  have hzero (x : s) : algebraMap R A x.1 = 0 :=
    hs.le (Ideal.subset_span x.2)
  choose m hm using fun x ↦ (IsLocalization.map_eq_zero_iff p.primeCompl A x.1).mp (hzero x)
  let r : p.primeCompl := ∏ x : s, m x
  have hker : RingHom.ker (algebraMap R A) ≤
      RingHom.ker (algebraMap R (Localization.Away r.1)) := by
    rw [← hs, Ideal.span_le]
    intro x hx
    apply (IsLocalization.map_eq_zero_iff (.powers r.1) _ _).mpr
    refine ⟨⟨r.1, 1, pow_one _⟩, ?_⟩
    change (∏ i : s, m i).1 * x = 0
    rw [Fintype.prod_eq_mul_prod_compl ⟨x, hx⟩, Submonoid.coe_mul,
      mul_assoc, mul_left_comm, hm, mul_zero]
  let φ : Localization.Away r.1 →+* A :=
    IsLocalization.Away.lift r.1 (IsLocalization.map_units A r)
  have hφ : Function.Injective φ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (.powers r.1) φ).mpr
    intro x y
    constructor
    · exact congrArg φ
    · intro hxy
      rw [← sub_eq_zero, ← map_sub]
      apply hker
      change algebraMap R A (x - y) = 0
      simpa only [φ, IsLocalization.Away.lift_eq, map_sub, sub_eq_zero] using hxy
  exact ⟨r.1, r.2, hφ.isDomain⟩

end FLT.Mazur.FCurve
