/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCubicPreimages
public import FLT.Mazur.ModuleSectionRatioAlongMorphism

/-!
# The original marking evaluated on the Y generator chart

Lift the actual marking to the original Y generator open and evaluate its
section ratios in the retained tensor frame. Both the scalar map and all three
coordinates are computed over the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e
open WeierstrassIntegralChart

local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "B" => Scheme.Opens.topIso (X := G.left) (U)

/-- The original marking factors through the Y generator open. -/
def relativePointMarkingY : S ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι s.left (by
    rw [Scheme.Opens.range_ι]
    exact sectionPoleGenerator_contains_marking s.left hI e 3 (T 1)
      (relativePointProjectiveY_coefficient G hg s hI e))

/-- This lift is the original marking after the actual open inclusion. -/
@[reassoc] theorem relativePointMarkingY_ι :
    relativePointMarkingY G hg s hI e ≫ (U).ι = s.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual normalized ratios on the Y chart evaluate to [0, 1, 0]. -/
theorem relativePointMarkingY_ratio (i : Fin 3) :
    (relativePointMarkingY G hg s hI e).appTop
      ((B).inv (sectionRatioOn (tensorPower (L) 3) (T 1) (U) le_rfl (T i))) =
        (![0, 1, 0] : Fin 3 → Γ(S, ⊤)) i := by
  erw [openFactor_appTop s.left (U)
    (relativePointMarking_preimage_yGenerator G hg s hI e).ge
    _ (relativePointMarkingY_ι G hg s hI e)]
  have h := sectionRatioOn_frame s.left (tensorPower (L) 3) (U)
    (relativePointMarking_preimage_yGenerator G hg s hI e).ge (T 1) (T i) le_rfl
    (sectionPoleMultiplicativeFrame s.left hI e 3)
    (relativePointProjectiveY_coefficient G hg s hI e)
  exact h.trans (relativePointProjectiveSections_coefficient G hg s hI e i)

/-- The actual chart scalar map restricts to the identity along the original marking. -/
theorem relativePointMarkingY_scalar (a : Γ(S, ⊤)) :
    (relativePointMarkingY G hg s hI e).appTop
      ((B).inv (sectionChartScalars G.hom.appTop.hom (U) a)) = a := by
  erw [openFactor_appTop s.left (U)
    (relativePointMarking_preimage_yGenerator G hg s hI e).ge
    _ (relativePointMarkingY_ι G hg s hI e)]
  unfold sectionChartScalars
  change s.left.appLE (U) ⊤ _ (G.left.presheaf.map _ (G.hom.appTop a)) = a
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_eq_app]
  change (s.left ≫ G.hom).appTop a = a
  rw [s.w]
  rfl

end FLT.Mazur.FCurve
