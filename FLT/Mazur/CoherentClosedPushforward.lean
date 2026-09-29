/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPushforwardRestriction

/-!
# Coherent pushforward along closed immersions

Pushforward along an isomorphism agrees with restriction along its inverse.
This transports the affine closed-immersion theorem from spectra to arbitrary
affine schemes. The open restriction comparison then proves local finite
presentation of closed pushforward over a locally Noetherian target.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X Y : Scheme.{u}}

/-- Pushforward by an isomorphism is restriction by the inverse isomorphism. -/
def pushforwardIsoRestrictInverse (e : X ≅ Y) :
    pushforward e.hom ≅ restrictFunctor e.inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (restrictFunctorAdjCounitIso e.inv).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId X) _ ≪≫
    Functor.leftUnitor _

/-- Pushforward along a scheme isomorphism preserves local finite presentation. -/
lemma coherentPresentation_pushforwardIso (e : X ≅ Y)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward e.hom).obj M).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrictInverse e).app M).symm
    (coherentPresentation_restrict e.inv M)

/-- Closed pushforward preserves coherence on an arbitrary Noetherian affine target. -/
theorem affineSchemeClosedPushforward_isFinitePresentation [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation := by
  obtain ⟨hX, hf⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  have : IsAffine X := hX
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let N := (pushforward X.isoSpec.hom).obj M
  have : N.IsFinitePresentation := coherentPresentation_pushforwardIso X.isoSpec M
  let P := (pushforward (Spec.map f.appTop)).obj N
  have : P.IsFinitePresentation :=
    affineClosedPushforward_isFinitePresentation f.appTop hf N
  have hcomp : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  let e : (pushforward Y.isoSpec.inv).obj P ≅ (pushforward f).obj M :=
    (pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).app N ≪≫
      (pushforwardComp X.isoSpec.hom (Spec.map f.appTop ≫ Y.isoSpec.inv)).app M ≪≫
      (pushforwardCongr hcomp).app M
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso e
    (coherentPresentation_pushforwardIso Y.isoSpec.symm P)

/-- A closed immersion into a locally Noetherian scheme preserves coherent module sheaves. -/
theorem closedPushforward_isFinitePresentation [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation := by
  apply coherentPresentation_of_affine_restrict
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : (M.restrict (f ⁻¹ᵁ U.1).ι).IsFinitePresentation :=
    coherentPresentation_restrict _ M
  have hP : ((pushforward (f ∣_ U.1)).obj
      (M.restrict (f ⁻¹ᵁ U.1).ι)).IsFinitePresentation :=
    affineSchemeClosedPushforward_isFinitePresentation _ _
  have : (((pushforward f).obj M).restrict U.1.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf).prop_of_iso
      ((closedPushforwardRestriction f U.1).app M).symm hP
  exact (SheafOfModules.isFinitePresentation (Spec Γ(Y, U.1)).ringCatSheaf).prop_of_iso
    ((restrictFunctorComp U.2.isoSpec.inv U.1.ι).app ((pushforward f).obj M)).symm
    (coherentPresentation_restrict U.2.isoSpec.inv _)

/-- In particular, the inclusion of the reduced closed subscheme preserves coherence. -/
theorem reducedClosedSubschemePushforward_isFinitePresentation [IsLocallyNoetherian Y]
    (Z : Closeds Y) (M : (reducedClosedSubscheme Z).Modules) [M.IsFinitePresentation] :
    ((pushforward (reducedClosedSubschemeι Z)).obj M).IsFinitePresentation :=
  closedPushforward_isFinitePresentation _ M

/-- Coherent sheaves on the constructed closed support push forward to coherent sheaves. -/
theorem supportSubschemePushforward_isFinitePresentation [IsLocallyNoetherian Y]
    (N : Y.Modules) [N.IsFinitePresentation]
    (M : (supportSubscheme N).Modules) [M.IsFinitePresentation] :
    ((pushforward (supportSubschemeι N)).obj M).IsFinitePresentation :=
  closedPushforward_isFinitePresentation _ M

end FLT.Mazur.FCurve.CoherentDevissage
