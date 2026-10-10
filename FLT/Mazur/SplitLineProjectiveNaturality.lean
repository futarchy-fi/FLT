/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineAffinePresentation
public import FLT.Mazur.LocallySplitSheafPullback
public import FLT.Mazur.LocallyFramedSplitLineNaturality

/-!
# Canonical locally split line points and base change

Local rank one and local splitting suffice for the global projective map,
its affine test-map law, and its naturality under every scheme morphism.
All pulled local hypotheses are proved from the original sheaf data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLineAffinePresentation
open FCurve SplitLineAffineNeighborhood ProjectiveSpace AffineSplitLineCoordinates
variable {X Y : Scheme.{u}} {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι) (hL : LocallyFreeRankOne L) (hs : LocallySplit s)

/-- The canonical reverse map lies over the original global coefficient spectrum. -/
lemma morphism_baseProjection :
    morphism s hL hs ≫ baseProjection Γ(X, ⊤) ι = X.toSpecΓ :=
  LocallyFramedSplitLineProjective.morphism_baseProjection s
    (ofLocal s hL hs).cover (ofLocal s hL hs).frame
    (ofLocal s hL hs).retraction (ofLocal s hL hs).split

/-- Every actual affine framed split test map recovers the canonical reverse point. -/
lemma morphism_affine_test {T : Scheme.{u}} [IsAffine T] (f : T ⟶ X)
    (d : (pullback f).obj L ≅ structureModule T)
    (q : SheafOfModules.free ι ⟶ (pullback f).obj L)
    (hq : SplitSheafLinePullback.inclusion f s ≫ q = 𝟙 _) :
    f ≫ morphism s hL hs =
      projectivePoint d (SplitSheafLinePullback.inclusion f s) q hq ≫
        coefficientMap f.appTop.hom ι :=
  LocallyFramedSplitLineProjective.affine_test s
    (ofLocal s hL hs).cover (ofLocal s hL hs).frame
    (ofLocal s hL hs).retraction (ofLocal s hL hs).split f d q hq

/-- Geometric naturality needs no chosen cover or hypotheses on the pulled inclusion. -/
lemma morphism_pullback (f : Y ⟶ X) :
    f ≫ morphism s hL hs =
      morphism (SplitSheafLinePullback.inclusion f s) (hL.pullback f) (hs.inclusion f) ≫
        coefficientMap f.appTop.hom ι := by
  let P := ofLocal s hL hs
  let Q := ofLocal (SplitSheafLinePullback.inclusion f s) (hL.pullback f) (hs.inclusion f)
  exact LocallyFramedSplitLineProjective.morphism_pullback s
    P.cover P.frame P.retraction P.split f Q.cover Q.frame Q.retraction Q.split

end FLT.Mazur.SplitLineAffinePresentation
