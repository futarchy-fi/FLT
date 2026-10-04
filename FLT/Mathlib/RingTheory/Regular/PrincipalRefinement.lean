/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.PrincipalNeighbourhood

/-! # Refine a principal regular-sequence neighbourhood around a fixed prime -/

@[expose] public noncomputable section

namespace RingTheory.Sequence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Inverting a multiple preserves weak regularity on a principal localization. -/
theorem isWeaklyRegular_away_of_dvd {a b : R} (hab : a ∣ b) (rs : List R)
    (h : IsWeaklyRegular (LocalizedModule.Away a M)
      (rs.map (algebraMap R (Localization.Away a)))) :
    IsWeaklyRegular (LocalizedModule.Away b M)
      (rs.map (algebraMap R (Localization.Away b))) := by
  apply (isWeaklyRegular_localizedModule_iff _ rs).mpr
  intro i hi
  let Q := M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M)
  let φ := LinearMap.lsmul R Q rs[i]
  have hφ := (isSMulRegular_localizedModule_iff _ _).mp
    ((isWeaklyRegular_localizedModule_iff _ rs).mp h i hi)
  apply (isSMulRegular_localizedModule_iff _ _).mpr
  apply (LinearMap.localizedMap_injective_iff_subsingleton_localized_ker _ φ).mpr
  apply LocalizedModule.subsingleton_iff_support_subset.mpr
  have hs := LocalizedModule.subsingleton_iff_support_subset.mp
    ((LinearMap.localizedMap_injective_iff_subsingleton_localized_ker _ φ).mp hφ)
  intro q hq x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact q.asIdeal.mem_of_dvd hab (hs hq (Set.mem_singleton _))

/-- Keep the terminal quotient nonzero when refining around the original prime. -/
theorem isRegular_away_of_dvd_of_atPrime (p : Ideal R) [p.IsPrime]
    {a b : R} (hab : a ∣ b) (hb : b ∉ p) (rs : List R)
    (ha : IsWeaklyRegular (LocalizedModule.Away a M)
      (rs.map (algebraMap R (Localization.Away a))))
    (hp : IsRegular (LocalizedModule p.primeCompl M)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    IsRegular (LocalizedModule.Away b M)
      (rs.map (algebraMap R (Localization.Away b))) := by
  refine ⟨isWeaklyRegular_away_of_dvd hab rs ha, fun hz ↦ ?_⟩
  have hs := LocalizedModule.subsingleton_iff_support_subset.mp
    ((localized_terminal_quotient_subsingleton_iff _ rs).mpr hz)
  have hsupport : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
      Module.support R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) := by
    by_contra hn
    exact hp.2 ((localized_terminal_quotient_subsingleton_iff _ rs).mp
      (Module.notMem_support_iff.mp hn))
  exact hb (hs hsupport (Set.mem_singleton _))

/-- Ring form of refinement, retaining the original coefficients. -/
theorem isRegular_ring_away_of_dvd_of_atPrime (p : Ideal R) [p.IsPrime]
    {a b : R} (hab : a ∣ b) (hb : b ∉ p) (rs : List R)
    (ha : IsRegular (Localization.Away a) (rs.map (algebraMap R (Localization.Away a))))
    (hp : IsRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    IsRegular (Localization.Away b) (rs.map (algebraMap R (Localization.Away b))) := by
  let e (T : Submonoid R) : LocalizedModule T R ≃ₗ[Localization T] Localization T :=
    (IsLocalizedModule.iso T (Algebra.linearMap R (Localization T))).extendScalarsOfIsLocalization
      T (Localization T)
  exact ((e (Submonoid.powers b)).isRegular_congr _).mp <|
    isRegular_away_of_dvd_of_atPrime p hab hb rs
      (((e (Submonoid.powers a)).isRegular_congr _).mpr ha).1
      (((e p.primeCompl).isRegular_congr _).mpr hp)

end RingTheory.Sequence
