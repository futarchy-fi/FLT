/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingCofinal
public import FLT.Mazur.AffineCohomologyVanishingRelCoordinates
public import FLT.Mazur.LocalizationCechExact

/-!
# Relative principal-cover exactness for tilde modules

A principal family covering `D(r)` becomes a unit-ideal family over `R_r`.
Localization-Cech exactness over that ring therefore gives exactness of the
actual relative sheaf Cech complex through the localization-in-stages comparison.
This verifies the cofinal-cover criterion for every tilde module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineCohomologyVanishingRelExact

open AffineCohomologyVanishingRelCoordinates AffineCohomologyVanishingCofinal

variable {R : CommRingCat.{u}} (r : R) {ι : Type u} (f : ι → R)
    (hf : (⨆ i, PrimeSpectrum.basicOpen (f i)) = PrimeSpectrum.basicOpen r)

include hf in
/-- A relative principal cover pulls back to a cover of the localized spectrum. -/
lemma localizedFamily_cover :
    (⨆ i, PrimeSpectrum.basicOpen (localizedFamily r f i)) = ⊤ := by
  apply top_unique
  intro x _
  have hx : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) x ∈
      PrimeSpectrum.basicOpen r := by
    change _ ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact ⟨x, rfl⟩
  rw [← hf] at hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

include hf in
/-- The image family generates the unit ideal after localizing at the covered open. -/
lemma localizedFamily_span : Ideal.span (Set.range (localizedFamily r f)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp (localizedFamily_cover r f hf)

variable [Finite ι] (M : ModuleCat.{u} R)

include hf in
/-- Tilde modules have exact positive Cech degrees on every finite relative principal cover. -/
theorem relative_principal_cech_exactAt (q : ℕ) :
    (CechSheafHZero.C (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (FCurve.moduleAbelianSheaf (tilde M))).ExactAt (q + 1) := by
  have h := LocalizationCechExact.exactAt_succ (localizedFamily r f)
    (localizedModule M r) (localizedFamily_span r f hf) q
  change ((LocalizationCech.complex (localizedFamily r f) (localizedModule M r)).sc
    (q + 1)).Exact at h
  have hres :
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).mapHomologicalComplex
        (.up ℕ)).obj (LocalizationCech.complex (localizedFamily r f)
        (localizedModule M r))).ExactAt (q + 1) :=
    h.map (ModuleCat.restrictScalars (algebraMap R (Localization.Away r)))
  have hmap :
      (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).mapHomologicalComplex
          (.up ℕ)).obj (LocalizationCech.complex (localizedFamily r f)
            (localizedModule M r)))).ExactAt (q + 1) :=
    hres.map (forget₂ (ModuleCat R) AddCommGrpCat)
  exact hmap.of_iso (relativeCechIso M r f hf).symm

/-- Every affine tilde module satisfies the all-degree cofinal-cover criterion. -/
theorem tilde_principalCoverExact (M : ModuleCat.{u} R) :
    PrincipalCoverExact (R := R) (FCurve.moduleAbelianSheaf (tilde M)) := by
  intro r ι hι f hf q
  exact relative_principal_cech_exactAt r f hf M q

end FLT.Mazur.AffineCohomologyVanishingRelExact
