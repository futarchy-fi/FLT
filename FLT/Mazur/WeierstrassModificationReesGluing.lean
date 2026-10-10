/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesSchemeOverlap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The glued fraction atlas is the equation modification

The isomorphism of chart spans induces an isomorphism of their pushouts.
This compares actual fraction charts, without asserting a Proj identification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The two actual fraction charts glued along the original generator ratio opens. -/
def fractionAtlas : Scheme :=
  pushout (horizontalOpenInclusion W s) (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs)

/-- The horizontal chart of the fraction atlas. -/
def horizontalChart : Spec (.of (WeierstrassModificationX.horizontalReesChart W s)) ⟶
    fractionAtlas W s b3 b4 b6 h3 h4 h6 hs := pushout.inl _ _

/-- The scale chart of the fraction atlas. -/
def scaleChart : Spec (.of (WeierstrassDilatation.scaleReesChart W s)) ⟶
    fractionAtlas W s b3 b4 b6 h3 h4 h6 hs := pushout.inr _ _

instance horizontalChart_isOpenImmersion :
    IsOpenImmersion (horizontalChart W s b3 b4 b6 h3 h4 h6 hs) := by
  change IsOpenImmersion (colimit.ι
    (span (horizontalOpenInclusion W s) (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs))
      WalkingSpan.left)
  infer_instance

instance scaleChart_isOpenImmersion :
    IsOpenImmersion (scaleChart W s b3 b4 b6 h3 h4 h6 hs) := by
  change IsOpenImmersion (colimit.ι
    (span (horizontalOpenInclusion W s) (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs))
      WalkingSpan.right)
  infer_instance

/-- The fraction atlas is isomorphic to the existing equation modification. -/
def fractionAtlasIso : fractionAtlas W s b3 b4 b6 h3 h4 h6 hs ≅
    WeierstrassModificationX.modification W s b3 b4 b6 :=
  asIso (pushout.map _ _ _ _ (horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom
    (scaleChartIso W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs)).hom
    (horizontalOverlapIso W s b3 b4 b6 h3 h4 h6 hs).hom
    (horizontalOverlapIso_inclusion W s b3 b4 b6 h3 h4 h6 hs)
    (horizontalOverlapIso_toScale W s b3 b4 b6 h3 h4 h6 hs))

/-- The global comparison restricts to the horizontal chart algebra equivalence. -/
@[reassoc (attr := simp)] theorem horizontalChart_atlasIso :
    horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫
        (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom =
      (horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationX.xChart W s b3 b4 b6 :=
  pushout.inl_desc _ _ _

/-- The global comparison restricts to the divided chart algebra equivalence. -/
@[reassoc (attr := simp)] theorem scaleChart_atlasIso :
    scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫
        (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom =
      (scaleChartIso W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs)).hom ≫
        WeierstrassModificationX.dividedChart W s b3 b4 b6 :=
  pushout.inr_desc _ _ _

/-- The two fraction inclusions agree on the prescribed common ratio open. -/
theorem fractionChart_overlap :
    horizontalOpenInclusion W s ≫ horizontalChart W s b3 b4 b6 h3 h4 h6 hs =
      horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs ≫
        scaleChart W s b3 b4 b6 h3 h4 h6 hs := pushout.condition

/-- Both constructed fraction charts together cover the global fraction atlas. -/
theorem fraction_charts_cover (z : fractionAtlas W s b3 b4 b6 h3 h4 h6 hs) :
    (∃ a, horizontalChart W s b3 b4 b6 h3 h4 h6 hs a = z) ∨
      ∃ a, scaleChart W s b3 b4 b6 h3 h4 h6 hs a = z := by
  obtain ⟨i, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (horizontalOpenInclusion W s) (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs)) z
  cases i with
  | none =>
    left
    refine ⟨horizontalOpenInclusion W s a, ?_⟩
    change (horizontalOpenInclusion W s ≫ horizontalChart W s b3 b4 b6 h3 h4 h6 hs) a = z
    rw [show horizontalOpenInclusion W s ≫ horizontalChart W s b3 b4 b6 h3 h4 h6 hs =
      colimit.ι (span (horizontalOpenInclusion W s)
        (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs)) WalkingSpan.zero from
          colimit.w (span (horizontalOpenInclusion W s)
            (horizontalOverlapToScale W s b3 b4 b6 h3 h4 h6 hs)) WalkingSpan.Hom.fst]
    exact ha
  | some i =>
    cases i with
    | left => exact Or.inl ⟨a, ha⟩
    | right => exact Or.inr ⟨a, ha⟩

end FLT.Mazur.WeierstrassModificationReesCoordinates
