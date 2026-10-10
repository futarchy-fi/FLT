/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TildeFiniteFreeLocalization
public import FLT.Mazur.AffineModuleGlobalSections
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Local finite free sheaves from finite projective modules

Finite projectivity constructs local bases and actual free sheaf charts.
These charts pull back along arbitrary morphisms, including the canonical
affine presentation, so the result applies to any affine scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FCurve

/-- Finite free charts on actual open subschemes, with rank allowed to vary. -/
def LocallyFiniteFree {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ ∃ (ι : Type u), Finite ι ∧
    Nonempty (M.restrict U.ι ≅ SheafOfModules.free ι)

/-- Finite local freeness is invariant under actual sheaf isomorphisms. -/
theorem LocallyFiniteFree.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : LocallyFiniteFree M) (e : M ≅ N) : LocallyFiniteFree N := by
  intro x
  obtain ⟨U, hx, ι, hι, ⟨t⟩⟩ := hM x
  exact ⟨U, hx, ι, hι, ⟨((restrictFunctor U.ι).mapIso e).symm ≪≫ t⟩⟩

/-- Arbitrary pullback preserves finite free charts. -/
theorem LocallyFiniteFree.pullback {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : LocallyFiniteFree M) (f : X ⟶ Y) : LocallyFiniteFree ((pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ι, hι, ⟨t⟩⟩ := hM (f x)
  exact ⟨f ⁻¹ᵁ U, hx, ι, hι, ⟨modulePullbackOpenIso f U M ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso t ≪≫
      ModuleGlobalEvaluationPullback.freeIso (f ∣_ U) ι⟩⟩

/-- Restriction preserves local finite freeness. -/
theorem LocallyFiniteFree.restrict {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : LocallyFiniteFree M) (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyFiniteFree (M.restrict f) :=
  (hM.pullback f).of_iso ((restrictFunctorIsoPullback f).app M).symm

/-- Finite projective modules have free principal localizations near every prime. -/
theorem finiteProjective_free_neighborhood {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] (x : PrimeSpectrum R) :
    ∃ r ∉ x.asIdeal, Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  let _ := Module.finitePresentation_of_projective R M
  let _ : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule.AtPrime x.asIdeal M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨r, hr, hf⟩

/-- The tilde of a finite projective module is locally finite free. -/
theorem finiteProjective_tilde_locallyFiniteFree {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] : LocallyFiniteFree (tilde M) := by
  intro x
  obtain ⟨r, hr, hf⟩ := finiteProjective_free_neighborhood M x
  let _ := hf
  obtain ⟨ι, hι, ht⟩ := TildeFiniteFreeLocalization.exists_basicOpenTrivialization M r
  exact ⟨PrimeSpectrum.basicOpen r, hr, ι, hι, ht⟩

/-- Affine reconstruction of a finite projective module has actual finite free charts. -/
theorem finiteProjective_affineTilde_locallyFiniteFree (S : Scheme.{u}) [IsAffine S]
    (M : ModuleCat.{u} Γ(S, ⊤)) [Module.Finite Γ(S, ⊤) M] [Module.Projective Γ(S, ⊤) M] :
    LocallyFiniteFree ((AffineModuleGlobalSections.affineTilde S).obj M) :=
  (finiteProjective_tilde_locallyFiniteFree M).pullback S.isoSpec.hom

end FLT.Mazur.FCurve
