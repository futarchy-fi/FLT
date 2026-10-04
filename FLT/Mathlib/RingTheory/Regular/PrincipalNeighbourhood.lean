/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.FiniteLocalizationInjectivity
public import FLT.Mathlib.RingTheory.Regular.LocalizationRegularity

/-! # Regular sequences spread from a prime to a principal neighbourhood -/

@[expose] public noncomputable section

namespace RingTheory.Sequence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A weakly regular sequence on a Noetherian module at a prime is weakly regular
on one principal neighbourhood, with the same original elements. -/
theorem exists_away_isWeaklyRegular_of_atPrime [IsNoetherian R M]
    (p : Ideal R) [p.IsPrime] (rs : List R)
    (h : IsWeaklyRegular (LocalizedModule p.primeCompl M)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ a ∉ p, IsWeaklyRegular (LocalizedModule.Away a M)
      (rs.map (algebraMap R (Localization.Away a))) := by
  let Q (i : Fin rs.length) := M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M)
  let φ (i : Fin rs.length) := LinearMap.lsmul R (Q i) rs[i]
  have hφ (i : Fin rs.length) : Function.Injective (LocalizedModule.map p.primeCompl (φ i)) :=
    (isSMulRegular_localizedModule_iff _ _).mp
      ((isWeaklyRegular_localizedModule_iff p.primeCompl rs).mp h i i.isLt)
  obtain ⟨a, ha, hφ⟩ := LinearMap.exists_away_injective_family p φ hφ
  refine ⟨a, ha, (isWeaklyRegular_localizedModule_iff _ rs).mpr fun i hi ↦ ?_⟩
  exact (isSMulRegular_localizedModule_iff _ _).mpr (hφ ⟨i, hi⟩)

/-- Vanishing of the localized terminal quotient is equivalent to the sequence
spanning the entire localized module. -/
theorem localized_terminal_quotient_subsingleton_iff (T : Submonoid R) (rs : List R) :
    Subsingleton (LocalizedModule T (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) ↔
    (⊤ : Submodule (Localization T) (LocalizedModule T M)) =
      Ideal.ofList (rs.map (algebraMap R (Localization T))) • ⊤ := by
  let e := localizedQuotientEquiv T (Ideal.ofList rs • (⊤ : Submodule R M))
  rw [← e.subsingleton_congr, Submodule.Quotient.subsingleton_iff]
  rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
    Submodule.localized'_top, Ideal.map_ofList, eq_comm]

/-- A regular sequence at a prime extends to a regular sequence on a principal
neighbourhood; the nonzero terminal quotient is retained. -/
theorem exists_away_isRegular_of_atPrime [IsNoetherian R M]
    (p : Ideal R) [p.IsPrime] (rs : List R)
    (h : IsRegular (LocalizedModule p.primeCompl M)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ a ∉ p, IsRegular (LocalizedModule.Away a M)
      (rs.map (algebraMap R (Localization.Away a))) := by
  obtain ⟨a, ha, hw⟩ := exists_away_isWeaklyRegular_of_atPrime p rs h.1
  refine ⟨a, ha, hw, fun hz ↦ ?_⟩
  have hs := (localized_terminal_quotient_subsingleton_iff _ rs).mpr hz
  have hsupport := LocalizedModule.subsingleton_iff_support_subset.mp hs
  have hp : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
      Module.support R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) := by
    by_contra hn
    exact h.2 ((localized_terminal_quotient_subsingleton_iff _ rs).mp
      (Module.notMem_support_iff.mp hn))
  exact ha (hsupport hp (Set.mem_singleton _))

/-- Ring form: a sequence regular in the local ring at a prime is regular after
inverting one element outside that prime. -/
theorem exists_isRegular_away_of_atPrime [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (rs : List R)
    (h : IsRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ a ∉ p, IsRegular (Localization.Away a)
      (rs.map (algebraMap R (Localization.Away a))) := by
  let e (T : Submonoid R) : LocalizedModule T R ≃ₗ[Localization T] Localization T :=
    (IsLocalizedModule.iso T (Algebra.linearMap R (Localization T))).extendScalarsOfIsLocalization
      T (Localization T)
  have hp := ((e p.primeCompl).isRegular_congr _).mpr h
  obtain ⟨a, ha, hr⟩ := exists_away_isRegular_of_atPrime p rs hp
  exact ⟨a, ha, ((e (Submonoid.powers a)).isRegular_congr _).mp hr⟩

end RingTheory.Sequence
