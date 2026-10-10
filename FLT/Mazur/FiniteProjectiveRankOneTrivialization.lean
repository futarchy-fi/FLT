/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveTildeLocal
public import FLT.Mazur.TildeInvertibleLocal

/-!
# Actual line trivializations from finite projective rank

A rank-one stalk of a finite projective module extends to a principal
neighborhood with an actual linear trivialization. Tilde transports this
to a trivialization on the original basic open of the spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry PrimeSpectrum
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
universe u
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- A linear trivialization of a principal localization trivializes the original tilde sheaf. -/
def tildeBasicOpenLinearTrivialization (r : R)
    (e : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) :
    (tilde M).restrict (Scheme.Opens.ι (X := Spec R) (basicOpen r)) ≅
      structureModule (Scheme.Opens.toScheme (X := Spec R) (basicOpen r)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let a : (tilde M).restrict f ≅ structureModule (Spec (.of (Localization.Away r))) :=
    (restrictFunctorIsoPullback f).app (tilde M) ≪≫
      ((AffineModulePullbackSections.tildePullbackIso _).app M).symm ≪≫
      (tilde.functor _).mapIso
        ((TildeFiniteFreeLocalization.localizationEquiv M r).trans e).toModuleIso ≪≫ tildeSelf
  let b := basicOpenIsoSpecAway r
  exact (restrictFunctorCongr (basicOpenIsoSpecAway_hom_SpecMap r).symm).app (tilde M) ≪≫
    (restrictFunctorComp b.hom f).app (tilde M) ≪≫
    (restrictFunctor b.hom).mapIso a ≪≫ restrictUnitIso b.hom

variable [Module.Finite R M] [Module.Projective R M]

/-- Rank one at one prime extends to a genuine principal linear trivialization. -/
lemma finiteProjective_rankOne_neighborhood (x : PrimeSpectrum R)
    (hx : Module.rankAtStalk (R := R) M x = 1) :
    ∃ r ∉ x.asIdeal, Nonempty
      (LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) := by
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
  refine ⟨r, hr, ⟨?_⟩⟩
  exact (Module.nonempty_linearEquiv_of_finrank_eq_one (hd.trans hx)).some.symm

/-- A rank-one stalk yields an actual sheaf frame on a principal neighborhood. -/
lemma finiteProjective_rankOne_sheafNeighborhood (x : PrimeSpectrum R)
    (hx : Module.rankAtStalk (R := R) M x = 1) :
    ∃ r ∉ x.asIdeal, Nonempty
      ((tilde M).restrict (Scheme.Opens.ι (X := Spec R) (basicOpen r)) ≅
        structureModule (Scheme.Opens.toScheme (X := Spec R) (basicOpen r))) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := finiteProjective_rankOne_neighborhood M x hx
  exact ⟨r, hr, ⟨tildeBasicOpenLinearTrivialization M r e⟩⟩

/-- Constant rank one constructs a line bundle, without assuming local trivializations. -/
theorem finiteProjective_tilde_rankOne
    (h : ∀ x : PrimeSpectrum R, Module.rankAtStalk (R := R) M x = 1) :
    LocallyFreeRankOne (tilde M) := by
  intro x
  obtain ⟨r, hr, he⟩ := finiteProjective_rankOne_sheafNeighborhood M x (h x)
  exact ⟨basicOpen r, hr, he⟩

/-- Every scheme mapping into the rank-one locus pulls back an actual line bundle. -/
theorem finiteProjective_tilde_pullback_rankOne {T : Scheme.{u}} (g : T ⟶ Spec R)
    (h : ∀ t : T, Module.rankAtStalk (R := R) M (g t) = 1) :
    LocallyFreeRankOne ((pullback g).obj (tilde M)) := by
  intro t
  obtain ⟨r, hr, ⟨e⟩⟩ := finiteProjective_rankOne_sheafNeighborhood M (g t) (h t)
  exact ⟨g ⁻¹ᵁ basicOpen r, hr, ⟨modulePullbackOpenIso g (basicOpen r) (tilde M) ≪≫
    (pullback (g ∣_ basicOpen r)).mapIso e ≪≫ modulePullbackUnitIso _⟩⟩

end FLT.Mazur.FCurve
