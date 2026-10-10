/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineProjectivePullback
public import FLT.Mazur.AffineSplitLineSourceTransport
public import FLT.Mazur.SplitSheafLinePullbackComposition
public import FLT.Mazur.ProjectiveCoefficientFunctor

/-!
# Refinement of actual local split-line projective points

For a sheaf inclusion on an arbitrary scheme, points recovered on affine
test charts agree after refinement to a common affine test map. The
comparison uses the genuine pullback composition isomorphism and arbitrary
frames and splittings; no projective compatibility is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open FCurve ProjectiveSpace
variable {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y]
variable (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z} (h : f ≫ g = k)
variable {ι : Type u} [Finite ι] {L : Z.Modules} (s : L ⟶ SheafOfModules.free ι)

include h in
/-- Original local split-line points agree on a genuine common affine refinement. -/
lemma projectivePoint_refinement
    (e : (pullback g).obj L ≅ structureModule Y)
    (d : (pullback k).obj L ≅ structureModule X)
    (r : SheafOfModules.free ι ⟶ (pullback g).obj L)
    (q : SheafOfModules.free ι ⟶ (pullback k).obj L)
    (hr : SplitSheafLinePullback.inclusion g s ≫ r = 𝟙 _)
    (hq : SplitSheafLinePullback.inclusion k s ≫ q = 𝟙 _) :
    f ≫ (projectivePoint e (SplitSheafLinePullback.inclusion g s) r hr ≫
      coefficientMap g.appTop.hom ι) =
        projectivePoint d (SplitSheafLinePullback.inclusion k s) q hq ≫
          coefficientMap k.appTop.hom ι := by
  let a := (pullbackComp f g).app L ≪≫ (pullbackCongr h).app L
  have hp := projectivePoint_sourceIso a (SplitSheafLinePullback.frame f e) d
    (SplitSheafLinePullback.inclusion f (SplitSheafLinePullback.inclusion g s))
    (SplitSheafLinePullback.inclusion k s) (SplitSheafLinePullback.retraction f r) q
    (SplitSheafLinePullback.inclusion_retraction f _ r hr) hq
    (SplitSheafLinePullback.inclusion_congr f g s h)
  rw [← Category.assoc, projectivePoint_pullback, hp, Category.assoc,
    coefficientMap_appTop_comp, h]


/-- Two arbitrary local frames agree on a common affine refinement; its frame is constructed. -/
lemma projectivePoint_common_refinement {W : Scheme.{u}} [IsAffine W]
    (a : W ⟶ X) (b : W ⟶ Y) (j : X ⟶ Z) (k : Y ⟶ Z)
    (hab : a ≫ j = b ≫ k)
    (e : (pullback j).obj L ≅ structureModule X)
    (d : (pullback k).obj L ≅ structureModule Y)
    (r : SheafOfModules.free ι ⟶ (pullback j).obj L)
    (q : SheafOfModules.free ι ⟶ (pullback k).obj L)
    (hr : SplitSheafLinePullback.inclusion j s ≫ r = 𝟙 _)
    (hq : SplitSheafLinePullback.inclusion k s ≫ q = 𝟙 _) :
    a ≫ (projectivePoint e (SplitSheafLinePullback.inclusion j s) r hr ≫
      coefficientMap j.appTop.hom ι) =
        b ≫ (projectivePoint d (SplitSheafLinePullback.inclusion k s) q hq ≫
          coefficientMap k.appTop.hom ι) := by
  let c := SplitSheafLinePullback.frameOver a j hab e
  let t := SplitSheafLinePullback.retractionOver a j hab r
  have ht := SplitSheafLinePullback.inclusion_retractionOver a j s hab r hr
  exact (projectivePoint_refinement a j hab s e c r t hr ht).trans
    (projectivePoint_refinement b k rfl s d c q t hq ht).symm

end FLT.Mazur.AffineSplitLineCoordinates
