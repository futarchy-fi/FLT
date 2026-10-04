/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePushforwardQuasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Coherence of finite direct images

Restriction of scalars along a finite ring map preserves finite modules.
Affine restriction transports this calculation to finite scheme morphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve
open CoherentDevissage

/-- Finite ring maps preserve the finiteness of actual pushforward sections. -/
lemma spectrumFinitePushforward_finite_sections {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (M : (Spec S).Modules) [M.IsFinitePresentation] :
    Module.Finite R (moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj M)) := by
  let := φ.hom.toAlgebra
  have : Module.Finite R S := hφ
  let N := moduleSpecΓFunctor.obj M
  have : Module.Finite S N := affineCoherent_finite_sections M
  let N' := (ModuleCat.restrictScalars φ.hom).obj N
  have : Module.Finite S N' := inferInstanceAs (Module.Finite S N)
  have : IsScalarTower R S N' := ⟨fun r s n ↦ mul_smul (φ r) s n⟩
  have : Module.Finite R N' := Module.Finite.trans S N'
  exact Module.Finite.equiv (affinePushforwardSectionsIso φ M).toLinearEquiv.symm

/-- Finite direct image on spectra preserves coherence over a Noetherian target. -/
lemma spectrumFinitePushforward_isFinitePresentation {R S : CommRingCat.{u}}
    [IsNoetherianRing R] (φ : R ⟶ S) (hφ : φ.hom.Finite)
    (M : (Spec S).Modules) [M.IsFinitePresentation] :
    ((pushforward (Spec.map φ)).obj M).IsFinitePresentation := by
  have hfinite := spectrumFinitePushforward_finite_sections φ hφ M
  have := spectrumPushforward_isQuasicoherent φ M
  exact (affineCoherent_iff_finite_sections _).mpr hfinite

variable {X Y : Scheme.{u}}

/-- Finite pushforward preserves coherence on a Noetherian affine target. -/
theorem affineSchemeFinitePushforward_isFinitePresentation [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let N := (pushforward X.isoSpec.hom).obj M
  have : N.IsFinitePresentation := coherentPresentation_pushforwardIso X.isoSpec M
  let P := (pushforward (Spec.map f.appTop)).obj N
  have : P.IsFinitePresentation :=
    spectrumFinitePushforward_isFinitePresentation f.appTop f.finite_appTop N
  have hcomp : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  let e : (pushforward Y.isoSpec.inv).obj P ≅ (pushforward f).obj M :=
    (pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).app N ≪≫
      (pushforwardComp X.isoSpec.hom (Spec.map f.appTop ≫ Y.isoSpec.inv)).app M ≪≫
      (pushforwardCongr hcomp).app M
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso e
    (coherentPresentation_pushforwardIso Y.isoSpec.symm P)

/-- A finite map to a locally Noetherian scheme preserves coherent module sheaves. -/
theorem finitePushforward_isFinitePresentation [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation := by
  apply coherentPresentation_of_affine_restrict
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : (M.restrict (f ⁻¹ᵁ U.1).ι).IsFinitePresentation :=
    coherentPresentation_restrict _ M
  have hP : ((pushforward (f ∣_ U.1)).obj
      (M.restrict (f ⁻¹ᵁ U.1).ι)).IsFinitePresentation :=
    affineSchemeFinitePushforward_isFinitePresentation _ _
  have : (((pushforward f).obj M).restrict U.1.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf).prop_of_iso
      ((closedPushforwardRestriction f U.1).app M).symm hP
  exact (SheafOfModules.isFinitePresentation (Spec Γ(Y, U.1)).ringCatSheaf).prop_of_iso
    ((restrictFunctorComp U.2.isoSpec.inv U.1.ι).app ((pushforward f).obj M)).symm
    (coherentPresentation_restrict U.2.isoSpec.inv _)

end FLT.Mazur.FCurve
