/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.LocalizationInjectivity
public import Mathlib.RingTheory.Regular.Flat

/-! # Regularity on localized modules and successive quotients -/

@[expose] public noncomputable section

namespace RingTheory.Sequence

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Localization of multiplication is multiplication on the localized module. -/
theorem localizedMap_lsmul (T : Submonoid R) (r : R) :
    (LocalizedModule.map T (LinearMap.lsmul R M r)).restrictScalars R =
      LinearMap.lsmul R (LocalizedModule T M) r := by
  apply IsLocalizedModule.linearMap_ext T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T M)
  ext m
  change IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T M) (LinearMap.lsmul R M r)
      (LocalizedModule.mkLinearMap T M m) = r • LocalizedModule.mkLinearMap T M m
  rw [IsLocalizedModule.map_apply]
  exact (LocalizedModule.mkLinearMap T M).map_smul r m

/-- The regularity of one element is detected by its localized multiplication map. -/
theorem isSMulRegular_localizedModule_iff (T : Submonoid R) (r : R) :
    IsSMulRegular (LocalizedModule T M) r ↔
      Function.Injective (LocalizedModule.map T (LinearMap.lsmul R M r)) := by
  rw [← LinearMap.coe_restrictScalars R, localizedMap_lsmul]
  rfl

/-- A regular element at a prime remains regular on a principal neighbourhood. -/
theorem exists_away_isSMulRegular_of_atPrime [IsNoetherian R M]
    (p : Ideal R) [p.IsPrime] (r : R)
    (h : IsSMulRegular (LocalizedModule p.primeCompl M) r) :
    ∃ a ∉ p, IsSMulRegular (LocalizedModule.Away a M) r := by
  obtain ⟨a, ha, hφ⟩ := LinearMap.exists_localizedMap_away_injective_of_atPrime p
    (LinearMap.lsmul R M r) ((isSMulRegular_localizedModule_iff _ _).mp h)
  exact ⟨a, ha, (isSMulRegular_localizedModule_iff _ _).mpr hφ⟩

/-- Regularity on a quotient of a localized module can be checked by localizing the
original quotient; this retains the original coefficients of the sequence. -/
theorem isSMulRegular_localized_quotient_iff (T : Submonoid R) (rs : List R) (r : R) :
    IsSMulRegular (LocalizedModule T M ⧸
      (Ideal.ofList (rs.map (algebraMap R (Localization T))) • ⊤ :
        Submodule (Localization T) (LocalizedModule T M)))
      (algebraMap R (Localization T) r) ↔
    IsSMulRegular (LocalizedModule T (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) r := by
  let e := localizedQuotientEquiv T (Ideal.ofList rs • (⊤ : Submodule R M))
  have he := e.toEquiv.isSMulRegular_congr (r := algebraMap R (Localization T) r) (s := r)
    (fun x ↦ by
      change e (_ • x) = r • e x
      rw [← algebraMap_smul (Localization T) r, e.map_smul])
  have hsub : (Ideal.ofList rs • (⊤ : Submodule R M)).localized T =
      Ideal.ofList (rs.map (algebraMap R (Localization T))) •
        (⊤ : Submodule (Localization T) (LocalizedModule T M)) := by
    rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top, Ideal.map_ofList]
  rw [hsub] at he
  exact he

/-- Every regularity test for a localized sequence is a test on the localization of
one of the original finite quotient modules. -/
theorem isWeaklyRegular_localizedModule_iff (T : Submonoid R) (rs : List R) :
    IsWeaklyRegular (LocalizedModule T M) (rs.map (algebraMap R (Localization T))) ↔
    ∀ i (_ : i < rs.length),
      IsSMulRegular (LocalizedModule T (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M)))
        rs[i] := by
  simp only [isWeaklyRegular_iff, List.length_map, List.getElem_map]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [← List.map_take]
  exact isSMulRegular_localized_quotient_iff T (rs.take i) rs[i]

end RingTheory.Sequence
