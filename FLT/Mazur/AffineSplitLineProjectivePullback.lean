/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineCoordinatePullback
public import FLT.Mazur.AffineSplitLineFrameIndependence
public import FLT.Mazur.SplitLineProjectivePullback

/-!
# Naturality of the projective point recovered from a split sheaf inclusion

The actual sheaf pullback and the coefficient projective map form a
commuting square. Any frame and any retraction of the pulled inclusion
give that same point. This applies to every affine open restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open FCurve ProjectiveSpace
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {ι : Type u} [Finite ι] {L : Y.Modules} (e : L ≅ structureModule Y)
variable (s : L ⟶ SheafOfModules.free ι) (r : SheafOfModules.free ι ⟶ L)
variable (hs : s ≫ r = 𝟙 L)

/-- The original inclusion's projective point commutes with actual geometric pullback. -/
lemma projectivePoint_pullback :
    f ≫ projectivePoint e s r hs =
      projectivePoint (SplitSheafLinePullback.frame f e) (SplitSheafLinePullback.inclusion f s)
        (SplitSheafLinePullback.retraction f r)
        (SplitSheafLinePullback.inclusion_retraction f s r hs) ≫
          coefficientMap f.appTop.hom ι := by
  unfold projectivePoint
  have hv := vector_pullback f e s
  have hp := SplitLinePrincipalPoints.morphism_pullback f (vector e s)
    (retraction e r) (vector_retraction e s r hs)
    (retraction (SplitSheafLinePullback.frame f e) (SplitSheafLinePullback.retraction f r))
    (pulled_vector_retraction f e s r hs)
  exact hp.trans (by congr 2; exact hv.symm)

/-- An arbitrary pulled source frame and splitting give the same geometric pullback. -/
lemma projectivePoint_pullback_choices (d : (pullback f).obj L ≅ structureModule X)
    (q : SheafOfModules.free ι ⟶ (pullback f).obj L)
    (hq : SplitSheafLinePullback.inclusion f s ≫ q = 𝟙 _) :
    f ≫ projectivePoint e s r hs =
      projectivePoint d (SplitSheafLinePullback.inclusion f s) q hq ≫
        coefficientMap f.appTop.hom ι := by
  rw [projectivePoint_pullback]
  exact congrArg (· ≫ coefficientMap f.appTop.hom ι)
    (projectivePoint_choices d (SplitSheafLinePullback.frame f e) _ _ _ _ _)

/-- Affine local frames recover restrictions of the original global projective morphism. -/
lemma projectivePoint_open (U : Y.Opens) [IsAffine U.toScheme]
    (d : (pullback U.ι).obj L ≅ structureModule U.toScheme)
    (q : SheafOfModules.free ι ⟶ (pullback U.ι).obj L)
    (hq : SplitSheafLinePullback.inclusion U.ι s ≫ q = 𝟙 _) :
    U.ι ≫ projectivePoint e s r hs =
      projectivePoint d (SplitSheafLinePullback.inclusion U.ι s) q hq ≫
        coefficientMap U.ι.appTop.hom ι :=
  projectivePoint_pullback_choices U.ι e s r hs d q hq

end FLT.Mazur.AffineSplitLineCoordinates
