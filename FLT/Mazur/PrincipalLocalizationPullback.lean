/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationJointRestriction
public import FLT.Mazur.PrincipalAffineRefinement
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Ring coordinates on the pullback of a principal affine open

Pulling Spec R_s back along Spec f gives Spec S_(f s). Under Gamma-Spec,
restriction is the explicit localized ring map, not a sheaf-module conversion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace FLT.Mazur.PrincipalLocalizationPullback

open LocalizationJointRestriction PrincipalAffineRefinement
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The specified localization maps form the affine base-change square. -/
lemma isPullback (f : R →+* S) (s : R) :
    IsPullback (inclusion (f s)) (Spec.map (CommRingCat.ofHom (restriction f s)))
      (Spec.map (CommRingCat.ofHom f)) (inclusion s) := by
  let : IsLocalization ((Submonoid.powers s).map f) (Localization.Away (f s)) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  apply CommRingCat.isPushout_of_isLocalization f (restriction f s) _ (Submonoid.powers s)
  ext a
  exact restriction_algebraMap f s a

/-- The canonical affine identification of the categorical pullback. -/
def iso (f : R →+* S) (s : R) :
    Spec (.of (Localization.Away (f s))) ≅
      pullback (Spec.map (CommRingCat.ofHom f)) (inclusion s) :=
  (isPullback f s).isoPullback

/-- Global sections on the actual pullback have the expected localization ring. -/
def sectionsIso (f : R →+* S) (s : R) :
    Γ(pullback (Spec.map (CommRingCat.ofHom f)) (inclusion s), ⊤) ≅
      CommRingCat.of (Localization.Away (f s)) :=
  (Scheme.Γ.mapIso (iso f s).op) ≪≫ Scheme.ΓSpecIso _

/-- Gamma of the localized branch morphism is exactly the ring restriction. -/
lemma restriction_appTop (f : R →+* S) (s : R)
    (z : Γ(Spec (.of (Localization.Away s)), ⊤)) :
    (Scheme.ΓSpecIso (.of (Localization.Away (f s)))).hom
      ((Spec.map (CommRingCat.ofHom (restriction f s))).appTop z) =
        restriction f s ((Scheme.ΓSpecIso (.of (Localization.Away s))).hom z) :=
  congrArg (fun k ↦ k.hom z) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (restriction f s)))

end FLT.Mazur.PrincipalLocalizationPullback
