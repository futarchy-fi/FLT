/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveTildeLocal

/-!
# Finite projective frames of a prescribed rank

The stalk rank determines a basis on a principal neighborhood. The resulting
sheaf frame is indexed by Fin d, with exactly the specified number of sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry PrimeSpectrum
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : CommRingCat.{0}} (M : ModuleCat.{0} R)
  [Module.Finite R M] [Module.Projective R M]

/-- A finite projective stalk of rank d extends to an actual d-element local basis. -/
theorem finiteProjective_rank_basis_neighborhood (x : PrimeSpectrum R) (d : ℕ)
    (hx : Module.rankAtStalk (R := R) M x = d) :
    ∃ r ∉ x.asIdeal, Nonempty
      (Module.Basis (Fin d) (Localization.Away r) (LocalizedModule.Away r M)) := by
  let _ := Module.finitePresentation_of_projective R M
  let _ : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule.AtPrime x.asIdeal M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, hd⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  let _ := hf
  let j : Localization.Away r →+* Localization.AtPrime x.asIdeal :=
    IsLocalization.map (M := .powers r) (T := x.asIdeal.primeCompl) _
      (RingHom.id _) (Submonoid.powers_le.mpr hr)
  let _ := j.domain_nontrivial
  exact ⟨r, hr, ⟨Module.finBasisOfFinrankEq _ _ (hd.trans hx)⟩⟩

/-- The localized basis supplies an exact-rank sheaf frame on the original basic open. -/
theorem finiteProjective_rank_sheaf_neighborhood (x : PrimeSpectrum R) (d : ℕ)
    (hx : Module.rankAtStalk (R := R) M x = d) :
    ∃ r ∉ x.asIdeal, Nonempty
      ((tilde M).restrict (Scheme.Opens.ι (X := Spec R) (basicOpen r)) ≅
        SheafOfModules.free (Fin d)) := by
  obtain ⟨r, hr, ⟨b⟩⟩ := finiteProjective_rank_basis_neighborhood M x d hx
  exact ⟨r, hr, ⟨TildeFiniteFreeLocalization.basicOpenTrivialization M r b⟩⟩

/-- A constant finite projective rank gives exact-rank frames after arbitrary pullback. -/
theorem finiteProjective_rank_pullback_frame {T : Scheme.{0}} (g : T ⟶ Spec R)
    (d : ℕ) (t : T) (ht : Module.rankAtStalk (R := R) M (g t) = d) :
    ∃ U : T.Opens, t ∈ U ∧ Nonempty
      (((pullback g).obj (tilde M)).restrict U.ι ≅ SheafOfModules.free (Fin d)) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := finiteProjective_rank_sheaf_neighborhood M (g t) d ht
  exact ⟨g ⁻¹ᵁ basicOpen r, hr, ⟨modulePullbackOpenIso g (basicOpen r) (tilde M) ≪≫
    (pullback (g ∣_ basicOpen r)).mapIso e ≪≫
      ModuleGlobalEvaluationPullback.freeIso (g ∣_ basicOpen r) (Fin d)⟩⟩

end FLT.Mazur.FCurve
