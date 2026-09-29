/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CoherentClosedPushforward

/-!
# Quasi-coherence of affine direct images

Direct image along an affine morphism preserves quasi-coherence. The spectrum
calculation is transported to arbitrary affine schemes and then glued on the
affine opens of the target. No Noetherian or finite presentation assumption is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

open CoherentDevissage

variable {X Y : Scheme.{u}}

/-- Direct image along a scheme isomorphism preserves quasi-coherence. -/
lemma quasicoherent_pushforwardIso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward e.hom).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrictInverse e).app M).symm
    (inferInstanceAs (M.restrict e.inv).IsQuasicoherent)

/-- Restriction of scalars on spectra preserves quasi-coherence. -/
lemma spectrumPushforward_isQuasicoherent {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((pushforward (Spec.map φ)).obj M).IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr (isIso_fromTildeΓ_pushforward φ M)

/-- Direct image between affine schemes preserves quasi-coherence. -/
lemma affineSchemePushforward_isQuasicoherent [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let N := (pushforward X.isoSpec.hom).obj M
  let _quasicoherentN : N.IsQuasicoherent := quasicoherent_pushforwardIso X.isoSpec M
  let P := (pushforward (Spec.map f.appTop)).obj N
  let _quasicoherentP : P.IsQuasicoherent := spectrumPushforward_isQuasicoherent f.appTop N
  have hcomp : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  let e : (pushforward Y.isoSpec.inv).obj P ≅ (pushforward f).obj M :=
    (pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).app N ≪≫
      (pushforwardComp X.isoSpec.hom (Spec.map f.appTop ≫ Y.isoSpec.inv)).app M ≪≫
      (pushforwardCongr hcomp).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e
    (quasicoherent_pushforwardIso Y.isoSpec.symm P)

/-- Presentations on the affine charts give quasi-coherence on the whole scheme. -/
lemma quasicoherent_of_affine_restrict (M : X.Modules)
    (h : ∀ U : X.affineOpens, (M.restrict U.2.fromSpec).IsQuasicoherent) :
    M.IsQuasicoherent := by
  have presentations (U : X.affineOpens) : Nonempty (M.over U.1).Presentation := by
    let N := M.restrict U.2.fromSpec
    let _fromTildeIso : IsIso N.fromTildeΓ :=
      (isQuasicoherent_iff_isIso_fromTildeΓ N).mp (h U)
    let P := (presentationTilde (moduleSpecΓFunctor.obj N) Set.univ (by simp)
      _ (Submodule.span_eq _)).ofIsIso N.fromTildeΓ
    let E := overEquiv U.1
    let F := restrictFunctor U.2.isoSpec.hom ⋙ E.inverse
    let _restrictColimits : PreservesColimitsOfSize.{u, u}
        (restrictFunctor U.2.isoSpec.hom) := inferInstance
    let _functorColimits : PreservesColimitsOfSize.{u, u} F := comp_preservesColimits _ _
    let unitIso : SheafOfModules.unit (X.ringCatSheaf.over U.1) ≅
        F.obj (SheafOfModules.unit _) :=
      E.unitIso.app _ ≪≫ E.inverse.mapIso (restrictUnitIso U.2.isoSpec.hom).symm
    let e : F.obj N ≅ M.over U.1 :=
      E.inverse.mapIso
        ((restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).symm.app M ≪≫
          (restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app M ≪≫
          (overFunctorEquiv U.1).symm.app M) ≪≫ E.unitIso.symm.app _
    exact ⟨(P.map F unitIso).ofIsIso e.hom⟩
  let q : M.QuasicoherentData := {
    I := X.affineOpens
    X := fun U ↦ U.1
    coversTop := by
      rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
      exact iSup_affineOpens_eq_top X
    presentation := fun U ↦ (presentations U).some }
  exact q.isQuasicoherent

/-- Affine direct image preserves quasi-coherence, with no finiteness assumptions. -/
theorem affinePushforward_isQuasicoherent (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  apply quasicoherent_of_affine_restrict
  intro U
  let _targetAffine : IsAffine U.1.toScheme := U.2
  let _sourceAffine : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have hP := affineSchemePushforward_isQuasicoherent (f ∣_ U.1)
    (M.restrict (f ⁻¹ᵁ U.1).ι)
  let _restrictionQuasicoherent :
      (((pushforward f).obj M).restrict U.1.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
      ((closedPushforwardRestriction f U.1).app M).symm hP
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, U.1)).ringCatSheaf).prop_of_iso
    ((restrictFunctorComp U.2.isoSpec.inv U.1.ι).app ((pushforward f).obj M)).symm
    (inferInstanceAs
      ((((pushforward f).obj M).restrict U.1.ι).restrict U.2.isoSpec.inv).IsQuasicoherent)

end FLT.Mazur.FCurve
