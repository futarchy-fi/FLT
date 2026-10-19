/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiFiniteMinimalPrimePrincipalAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite Cartesian source over original minimal-prime principal opens

The finite localization is identified with the actual Cartesian scheme source.
The original minimal prime is in the image of the constructed target inclusion;
no integral or reduced replacement of its original coefficient ring is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SpecMinimalPrimeFiniteOpen
set_option backward.isDefEq.respectTransparency false
variable {R B : Type} [CommRing R] [CommRing B]
  (s : R →+* B) (r : R)

/-- The original principal target map. -/
def targetMap : Spec (.of (Localization.Away r)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))

instance targetMap_isOpenImmersion : IsOpenImmersion (targetMap (R := R) r) := by
  unfold targetMap
  infer_instance

/-- Finiteness of the full algebra gives finiteness of the actual Cartesian source. -/
theorem projection_isFinite
    (hf : (IsLocalization.Away.map (Localization.Away r)
      (Localization.Away (s r)) s r).Finite) :
    IsFinite (pullback.snd (Spec.map (CommRingCat.ofHom s)) (targetMap r)) := by
  let L := Localization.Away r
  let T := Localization.Away (s r)
  let τ : L →+* T := IsLocalization.Away.map L T s r
  have hc : τ.comp (algebraMap R L) = (algebraMap B T).comp s :=
    IsLocalization.map_comp (Submonoid.powers r).le_comap_map
  have H := (CommRingCat.isPushout_of_isLocalization s τ hc (Submonoid.powers r)).op.map
    Scheme.Spec
  let _ : IsFinite (Scheme.Spec.map (CommRingCat.ofHom τ).op) :=
    (IsFinite.SpecMap_iff _).mpr hf
  change IsFinite (pullback.snd (Scheme.Spec.map (CommRingCat.ofHom s).op)
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R L)).op))
  rw [← H.flip.isoPullback_inv_snd]
  infer_instance

/-- The constructed principal open contains precisely the primes avoiding its original scalar. -/
theorem mem_targetMap_range (P : PrimeSpectrum R) :
    P ∈ Set.range (targetMap r) ↔ r ∉ P.asIdeal := by
  change P ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) ↔ _
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
  rfl

variable [IsNoetherianRing R]

/-- Every original minimal prime has a whole-source finite principal neighborhood. -/
theorem exists_finite_principal (P : PrimeSpectrum R)
    (hP : P.asIdeal ∈ minimalPrimes R) (hs : s.QuasiFinite) (hf : s.FiniteType) :
    ∃ r : R, r ∉ P.asIdeal ∧
      IsFinite (pullback.snd (Spec.map (CommRingCat.ofHom s)) (targetMap r)) := by
  obtain ⟨r, hr, hfin⟩ :=
    QuasiFiniteMinimalPrimePrincipalAlgebra.exists_finite_principal s P hP hs hf
  exact ⟨r, hr, projection_isFinite s r hfin⟩

end FLT.Mazur.SpecMinimalPrimeFiniteOpen
