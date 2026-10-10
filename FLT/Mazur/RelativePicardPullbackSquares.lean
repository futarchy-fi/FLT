/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfCover

/-!
# Cartesian squares on relative Picard total spaces

Actual total-space restriction maps retain cartesian squares of test schemes.
The resulting overlap comparison retains both original projections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {P T U V : Over S} (a : P ⟶ U) (b : P ⟶ V) (g : U ⟶ T) (h : V ⟶ T)
  (H : IsPullback a.left b.left g.left h.left)

include H in
/-- A cartesian square of test schemes gives a cartesian square of actual total spaces. -/
theorem relativeTotalMap_square_isPullback :
    IsPullback (relativeTotalMap f a) (relativeTotalMap f b)
      (relativeTotalMap f g) (relativeTotalMap f h) := by
  have w : a ≫ g = b ≫ h := Over.OverMorphism.ext H.w
  have wt : relativeTotalMap f a ≫ relativeTotalMap f g =
      relativeTotalMap f b ≫ relativeTotalMap f h := by
    rw [← relativeTotalMap_comp, ← relativeTotalMap_comp, w]
  have outer := (relativeTotalMap_isPullback f b).flip.paste_horiz H
  have outer' : IsPullback
      (relativeTotalMap f a ≫ Limits.pullback.snd f U.hom)
      (relativeTotalMap f b) g.left
      (relativeTotalMap f h ≫ Limits.pullback.snd f T.hom) := by
    simpa only [relativeTotalMap_snd, Category.assoc] using outer
  exact outer'.of_right wt (relativeTotalMap_isPullback f g).flip

/-- The canonical comparison of the original total overlap with its fiber product. -/
def relativeTotalOverlapIso : Limits.pullback f P.hom ≅
    Limits.pullback (relativeTotalMap f g) (relativeTotalMap f h) :=
  (relativeTotalMap_square_isPullback f a b g h H).isoPullback

/-- The comparison preserves the first original projection. -/
@[reassoc]
theorem relativeTotalOverlapIso_fst :
    (relativeTotalOverlapIso f a b g h H).hom ≫ Limits.pullback.fst _ _ =
      relativeTotalMap f a :=
  (relativeTotalMap_square_isPullback f a b g h H).isoPullback_hom_fst

/-- The comparison preserves the second original projection. -/
@[reassoc]
theorem relativeTotalOverlapIso_snd :
    (relativeTotalOverlapIso f a b g h H).hom ≫ Limits.pullback.snd _ _ =
      relativeTotalMap f b :=
  (relativeTotalMap_square_isPullback f a b g h H).isoPullback_hom_snd

end FLT.Mazur.SchemePicard
