/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesSchemeOverlap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The glued fraction atlas is the equation modification

The isomorphism of chart spans induces an isomorphism of their pushouts.
This compares actual fraction charts, without asserting a Proj identification.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R) (hπ : π ≠ 0)

/-- The two actual fraction charts glued along the original generator ratio opens. -/
def fractionAtlas : Scheme :=
  pushout (horizontalOpenInclusion W s π b3 b4 b6) (horizontalOverlapToScale W s π b3 b4 b6 hπ)

/-- The horizontal chart of the fraction atlas. -/
def horizontalChart : Spec (.of (WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6)) ⟶
    fractionAtlas W s π b3 b4 b6 hπ := pushout.inl _ _

/-- The scale chart of the fraction atlas. -/
def scaleChart : Spec (.of (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)) ⟶
    fractionAtlas W s π b3 b4 b6 hπ := pushout.inr _ _

instance horizontalChart_isOpenImmersion :
    IsOpenImmersion (horizontalChart W s π b3 b4 b6 hπ) := by
  change IsOpenImmersion (colimit.ι
    (span (horizontalOpenInclusion W s π b3 b4 b6) (horizontalOverlapToScale W s π b3 b4 b6 hπ))
      WalkingSpan.left)
  infer_instance

instance scaleChart_isOpenImmersion :
    IsOpenImmersion (scaleChart W s π b3 b4 b6 hπ) := by
  change IsOpenImmersion (colimit.ι
    (span (horizontalOpenInclusion W s π b3 b4 b6) (horizontalOverlapToScale W s π b3 b4 b6 hπ))
      WalkingSpan.right)
  infer_instance

/-- The fraction atlas is isomorphic to the existing equation modification. -/
def fractionAtlasIso : fractionAtlas W s π b3 b4 b6 hπ ≅
    WeierstrassSuccessiveX.modification W s π b3 b4 b6 :=
  asIso (pushout.map _ _ _ _ (horizontalChartIso W s π b3 b4 b6 hπ).hom
    (scaleChartIso W s π b3 b4 b6 (IsRegular.of_ne_zero hπ)).hom
    (horizontalOverlapIso W s π b3 b4 b6 hπ).hom
    (horizontalOverlapIso_inclusion W s π b3 b4 b6 hπ)
    (horizontalOverlapIso_toScale W s π b3 b4 b6 hπ))

/-- The global comparison restricts to the horizontal chart algebra equivalence. -/
@[reassoc (attr := simp)] theorem horizontalChart_atlasIso :
    horizontalChart W s π b3 b4 b6 hπ ≫
        (fractionAtlasIso W s π b3 b4 b6 hπ).hom =
      (horizontalChartIso W s π b3 b4 b6 hπ).hom ≫
        WeierstrassSuccessiveX.xChart W s π b3 b4 b6 :=
  pushout.inl_desc _ _ _

/-- The global comparison restricts to the divided chart algebra equivalence. -/
@[reassoc (attr := simp)] theorem scaleChart_atlasIso :
    scaleChart W s π b3 b4 b6 hπ ≫
        (fractionAtlasIso W s π b3 b4 b6 hπ).hom =
      (scaleChartIso W s π b3 b4 b6 (IsRegular.of_ne_zero hπ)).hom ≫
        WeierstrassSuccessiveX.dividedChart W s π b3 b4 b6 :=
  pushout.inr_desc _ _ _

/-- The two fraction inclusions agree on the prescribed common ratio open. -/
theorem fractionChart_overlap :
    horizontalOpenInclusion W s π b3 b4 b6 ≫ horizontalChart W s π b3 b4 b6 hπ =
      horizontalOverlapToScale W s π b3 b4 b6 hπ ≫
        scaleChart W s π b3 b4 b6 hπ := pushout.condition

/-- Both constructed fraction charts together cover the global fraction atlas. -/
theorem fractionAtlas_charts_cover (z : fractionAtlas W s π b3 b4 b6 hπ) :
    (∃ a, horizontalChart W s π b3 b4 b6 hπ a = z) ∨
      ∃ a, scaleChart W s π b3 b4 b6 hπ a = z := by
  obtain ⟨i, a, ha⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (horizontalOpenInclusion W s π b3 b4 b6) (horizontalOverlapToScale W s π b3 b4 b6 hπ)) z
  cases i with
  | none =>
    left
    refine ⟨horizontalOpenInclusion W s π b3 b4 b6 a, ?_⟩
    change (horizontalOpenInclusion W s π b3 b4 b6 ≫ horizontalChart W s π b3 b4 b6 hπ) a = z
    rw [show horizontalOpenInclusion W s π b3 b4 b6 ≫ horizontalChart W s π b3 b4 b6 hπ =
      colimit.ι (span (horizontalOpenInclusion W s π b3 b4 b6)
        (horizontalOverlapToScale W s π b3 b4 b6 hπ)) WalkingSpan.zero from
          colimit.w (span (horizontalOpenInclusion W s π b3 b4 b6)
            (horizontalOverlapToScale W s π b3 b4 b6 hπ)) WalkingSpan.Hom.fst]
    exact ha
  | some i =>
    cases i with
    | left => exact Or.inl ⟨a, ha⟩
    | right => exact Or.inr ⟨a, ha⟩

end FLT.Mazur.WeierstrassSuccessiveRees
