/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.LocalizationInjectivity

/-! # A common principal neighbourhood for finitely many injectivity conditions -/

@[expose] public noncomputable section

namespace LinearMap

variable {R ι : Type*} [CommRing R] [Finite ι]
  {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- Finitely many maps with finite kernels that are injective at a prime become injective
on one common principal neighbourhood. -/
theorem exists_away_injective_family (p : Ideal R) [p.IsPrime]
    (φ : ∀ i, M i →ₗ[R] N i) [∀ i, Module.Finite R (LinearMap.ker (φ i))]
    (hφ : ∀ i, Function.Injective (LocalizedModule.map p.primeCompl (φ i))) :
    ∃ a ∉ p, ∀ i, Function.Injective (LocalizedModule.map (Submonoid.powers a) (φ i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose a ha h using fun i ↦ exists_localizedMap_away_injective_of_atPrime p (φ i) (hφ i)
  refine ⟨∏ i, a i, p.primeCompl.prod_mem (fun i _ ↦ ha i), fun i ↦ ?_⟩
  apply (localizedMap_injective_iff_subsingleton_localized_ker _ (φ i)).mpr
  apply LocalizedModule.subsingleton_iff_support_subset.mpr
  have hs := LocalizedModule.subsingleton_iff_support_subset.mp
    ((localizedMap_injective_iff_subsingleton_localized_ker _ (φ i)).mp (h i))
  intro q hq x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact q.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
    (hs hq (Set.mem_singleton _))

end LinearMap
