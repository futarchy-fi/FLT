/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChartPreimage

/-!
# Actual scheme base change of the glued translated Hilbert charts

The chart-preimage squares and the product parameter squares identify the
whole glued scheme with the scheme-theoretic pullback over its translation base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {V W : Over (Spec (.of R))} (b : W ⟶ V)
  {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
local notation "aW" => fun i ↦ baseMarkedIndexChange f b (a i)

/-- The descended scheme comparison is the actual translation-base pullback. -/
theorem baseMarkedGluedChange_isPullback :
    IsPullback (baseMarkedGluedChange f hL b a).left
      (baseMarkedGluedBase f hL W aW).left (baseMarkedGluedBase f hL V a).left b.left := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (baseMarkedGluedCover f hL V a)
  intro i
  change ι at i
  change IsPullback
    (pullback.snd (baseMarkedGluedChange f hL b a).left
      (baseMarkedGluedArrow f hL V a i).left)
    (pullback.fst (baseMarkedGluedChange f hL b a).left
      (baseMarkedGluedArrow f hL V a i).left ≫ (baseMarkedGluedBase f hL W aW).left)
    ((baseMarkedGluedArrow f hL V a i).left ≫ (baseMarkedGluedBase f hL V a).left) b.left
  let H := (baseMarkedGluedChange_chart_isPullback f hL b a i).map (Over.forget _)
  have hb := (baseMarkedChartChange_isPullback f b (a i).1).map (Over.forget _)
  apply hb.of_iso H.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact (Category.comp_id _).trans H.isoPullback_hom_snd.symm
  · exact (Category.comp_id _).trans
      ((congrArg Over.Hom.left (baseMarkedGluedArrow_base f hL W aW i)).symm.trans
        (H.isoPullback_hom_fst_assoc (baseMarkedGluedBase f hL W aW).left).symm)
  · exact (Category.comp_id _).trans
      ((congrArg Over.Hom.left (baseMarkedGluedArrow_base f hL V a i)).symm.trans
        (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- An explicit scheme isomorphism with the pullback, with both projections retained. -/
def baseMarkedGluedChangeIso :
    (baseMarkedGluedTest f hL W aW).left ≅
      pullback (baseMarkedGluedBase f hL V a).left b.left :=
  (baseMarkedGluedChange_isPullback f hL b a).isoPullback

@[reassoc]
theorem baseMarkedGluedChangeIso_fst :
    (baseMarkedGluedChangeIso f hL b a).hom ≫
        pullback.fst (baseMarkedGluedBase f hL V a).left b.left =
      (baseMarkedGluedChange f hL b a).left :=
  (baseMarkedGluedChange_isPullback f hL b a).isoPullback_hom_fst

@[reassoc]
theorem baseMarkedGluedChangeIso_snd :
    (baseMarkedGluedChangeIso f hL b a).hom ≫
        pullback.snd (baseMarkedGluedBase f hL V a).left b.left =
      (baseMarkedGluedBase f hL W aW).left :=
  (baseMarkedGluedChange_isPullback f hL b a).isoPullback_hom_snd

end FLT.Mazur.HilbertChart
