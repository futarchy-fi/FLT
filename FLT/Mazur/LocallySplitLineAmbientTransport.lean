/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineAmbientTransport
public import FLT.Mazur.SplitLineProjectiveNaturality
public import FLT.Mazur.LocallySplitSheafTransport

/-!
# Ambient transport with a nontrivial source line

On an affine base, the canonical reverse point respects an arbitrary
isomorphism between finite free ambient sheaves. Source frames and splitting
maps are constructed locally from the original sheaf hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitSheafLinePullback
open AffineFreeSheafCoordinates
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι κ : Type u} {L : Y.Modules}

/-- Pulling back an ambient composite uses the original canonical free comparison. -/
lemma inclusion_ambientIso (s : L ⟶ SheafOfModules.free ι)
    (a : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ) :
    inclusion f (s ≫ a.hom) = inclusion f s ≫ (pullbackFreeIso f a).hom := by
  simp only [inclusion, pullbackFreeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

end FLT.Mazur.SplitSheafLinePullback

namespace FLT.Mazur.SplitLineAffinePresentation
open FCurve SplitLineAffineNeighborhood ProjectiveSpace AffineSplitLineCoordinates
open AffineFreeSheafCoordinates FiniteFreeContragredient
variable {X : Scheme.{u}} [IsAffine X] {ι κ : Type u} [Finite ι] [Finite κ]
variable {L : X.Modules} (s : L ⟶ SheafOfModules.free ι)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
variable (a : (SheafOfModules.free ι : X.Modules) ≅ SheafOfModules.free κ)

/-- The canonical reverse map respects actual ambient coordinates without a global frame. -/
lemma morphism_ambientIso :
    morphism s hL hs ≫ (linearIso (map (coordinates X a))).hom =
      morphism (s ≫ a.hom) hL (hs.postcompose s a) := by
  let P := ofLocal s hL hs
  apply P.cover.hom_ext
  intro i
  let f := P.cover.f i
  let b := pullbackFreeIso f a
  let q := b.inv ≫ P.retraction i
  have hi := SplitSheafLinePullback.inclusion_ambientIso f s a
  have hq : SplitSheafLinePullback.inclusion f (s ≫ a.hom) ≫ q = 𝟙 _ := by
    rw [hi]
    exact ambientIso_retraction b (SplitSheafLinePullback.inclusion f s)
      (P.retraction i) (P.split i)
  have hp : projectivePoint (P.frame i) (SplitSheafLinePullback.inclusion f s)
      (P.retraction i) (P.split i) ≫ (linearIso (map (coordinates _ b))).hom =
        projectivePoint (P.frame i) (SplitSheafLinePullback.inclusion f (s ≫ a.hom))
          q hq := by
    have hp := projectivePoint_ambientIso b (P.frame i)
      (SplitSheafLinePullback.inclusion f s) (P.retraction i) (P.split i) q
      (by rw [← hi]; exact hq)
    exact hp.trans (by congr 1; exact hi.symm)
  change f ≫ (morphism s hL hs ≫ _) = f ≫ _
  rw [← Category.assoc, morphism_affine_test s hL hs f (P.frame i)
    (P.retraction i) (P.split i), Category.assoc,
    projective_coefficient _ _ _ (coordinates_pullback f a), ← Category.assoc, hp,
    morphism_affine_test (s ≫ a.hom) hL (hs.postcompose s a) f (P.frame i) q hq]

end FLT.Mazur.SplitLineAffinePresentation
