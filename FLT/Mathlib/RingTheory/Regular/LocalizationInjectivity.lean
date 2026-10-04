/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Support

/-! # Spreading injectivity from a stalk to a principal neighbourhood -/

@[expose] public noncomputable section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Injectivity after localization is the vanishing of the localized kernel. -/
theorem localizedMap_injective_iff_subsingleton_localized_ker
    (T : Submonoid R) (φ : M →ₗ[R] N) :
    Function.Injective (LocalizedModule.map T φ) ↔
      Subsingleton (LocalizedModule T (LinearMap.ker φ)) := by
  let f := LocalizedModule.mkLinearMap T M
  let g := LocalizedModule.mkLinearMap T N
  let :=  toKerLocalized_isLocalizedModule (Localization T) T f g φ
  let e := IsLocalizedModule.iso T (toKerIsLocalized T f g φ)
  rw [e.subsingleton_congr, Submodule.subsingleton_iff_eq_bot, ker_eq_bot]
  rfl

/-- A map with finite kernel that is injective at a prime is injective on a principal
neighbourhood of that prime. -/
theorem exists_localizedMap_away_injective_of_atPrime (p : Ideal R) [p.IsPrime]
    (φ : M →ₗ[R] N) [Module.Finite R (LinearMap.ker φ)]
    (hφ : Function.Injective (LocalizedModule.map p.primeCompl φ)) :
    ∃ a ∉ p, Function.Injective (LocalizedModule.map (Submonoid.powers a) φ) := by
  have :=  (localizedMap_injective_iff_subsingleton_localized_ker p.primeCompl φ).mp hφ
  obtain ⟨a, ha, h⟩ := LocalizedModule.exists_subsingleton_away p (M := LinearMap.ker φ)
  exact ⟨a, ha, (localizedMap_injective_iff_subsingleton_localized_ker _ φ).mpr h⟩

end LinearMap
