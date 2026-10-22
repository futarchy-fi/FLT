/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFrameCover
public import FLT.Mazur.GeneralizedCurveMarkingOpenGluing

/-!
# The actual whole-family morphism to the glued cubic

The original local cubic maps agree on every framed affine refinement. They
glue on the pullback cover of the entire original curve, recovering those
maps exactly and retaining its structure morphism to the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

local instance gluedMorphismNoetherian (i : SmoothMarkingAffineChart E s) :
    IsNoetherianRing Γ(i.base.1.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The actual original whole-curve map on a framed affine neighborhood. -/
def smoothMarkingLocalToGlued (i : SmoothMarkingAffineChart E s) :
    (E.baseChange i.base.1.ι).curve.left ⟶ smoothMarkingGluedCubic E s :=
  smoothMarkingToIntegralCubic (E.baseChange i.base.1.ι) (pullSection i.base.1.ι s) i.frame ≫
    smoothMarkingGluedChart E s i

/-- Actual whole-family restrictions retain the local maps to the glued cubic. -/
@[reassoc] theorem smoothMarkingLocalToGlued_naturality
    {i j : SmoothMarkingAffineChart E s} (f : i ⟶ j) :
    openRestrictionCurveMap E j.base.1 i.base.1 f.le ≫ smoothMarkingLocalToGlued E s j =
      smoothMarkingLocalToGlued E s i := by
  rw [smoothMarkingLocalToGlued, ← Category.assoc,
    ← smoothMarkingDirectRestriction_curve, Category.assoc]
  change _ ≫ (smoothMarkingAffineDiagram E s).map f ≫ smoothMarkingGluedChart E s j = _
  rw [smoothMarkingGluedChart_naturality]
  rfl

/-- The local maps satisfy the actual pullback cover's gluing condition. -/
theorem smoothMarkingLocalToGlued_compatible
    {i j : (smoothMarkingFrameCover E s).I₀} (f : i ⟶ j) :
    Scheme.Cover.trans ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom) f ≫
      smoothMarkingLocalToGlued E s j = smoothMarkingLocalToGlued E s i := by
  rw [smoothMarkingFrameCover_curveTrans E s f]
  exact smoothMarkingLocalToGlued_naturality E s f

/-- The actual whole original family maps to the glued cubic. -/
def smoothMarkingToGluedCubic : E.curve.left ⟶ smoothMarkingGluedCubic E s :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom)
    (smoothMarkingLocalToGlued E s) (smoothMarkingLocalToGlued_compatible E s)

/-- Restriction of the global morphism recovers each original whole-curve cubic map. -/
@[reassoc] theorem smoothMarkingToGluedCubic_chart (i : SmoothMarkingAffineChart E s) :
    Limits.pullback.fst E.curve.hom i.base.1.ι ≫ smoothMarkingToGluedCubic E s =
      smoothMarkingLocalToGlued E s i :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
    ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom)
    (smoothMarkingLocalToGlued E s) (smoothMarkingLocalToGlued_compatible E s) i

/-- Each original local whole-curve map retains its base morphism after gluing. -/
@[reassoc] theorem smoothMarkingLocalToGlued_over (i : SmoothMarkingAffineChart E s) :
    smoothMarkingLocalToGlued E s i ≫ smoothMarkingGluedBase E s =
      Limits.pullback.fst E.curve.hom i.base.1.ι ≫ E.curve.hom := by
  rw [smoothMarkingLocalToGlued, Category.assoc, smoothMarkingGluedChart_base]
  change smoothMarkingToIntegralCubic (E.baseChange i.base.1.ι)
    (pullSection i.base.1.ι s) i.frame ≫
    (integralCurveStructure (smoothMarkingWeierstrassCurve (E.baseChange i.base.1.ι)
      (pullSection i.base.1.ι s) i.frame) ≫ i.base.1.toScheme.isoSpec.inv ≫ i.base.1.ι) = _
  rw [← Category.assoc, smoothMarkingToIntegralCubic_over, Category.assoc]
  change (E.baseChange i.base.1.ι).curve.hom ≫
    i.base.1.toScheme.isoSpec.hom ≫ i.base.1.toScheme.isoSpec.inv ≫ i.base.1.ι = _
  rw [Iso.hom_inv_id_assoc]
  exact Limits.pullback.condition.symm

/-- The glued whole-family morphism retains the original structure map. -/
@[reassoc] theorem smoothMarkingToGluedCubic_over :
    smoothMarkingToGluedCubic E s ≫ smoothMarkingGluedBase E s = E.curve.hom := by
  apply Scheme.Cover.hom_ext ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom)
  intro i
  change Limits.pullback.fst E.curve.hom i.base.1.ι ≫ _ =
    Limits.pullback.fst E.curve.hom i.base.1.ι ≫ E.curve.hom
  rw [← Category.assoc, smoothMarkingToGluedCubic_chart, smoothMarkingLocalToGlued_over]

/-- The actual local whole-curve maps uniquely determine the global morphism. -/
theorem smoothMarkingToGluedCubic_unique (f : E.curve.left ⟶ smoothMarkingGluedCubic E s)
    (hf : ∀ i : SmoothMarkingAffineChart E s,
      Limits.pullback.fst E.curve.hom i.base.1.ι ≫ f = smoothMarkingLocalToGlued E s i) :
    f = smoothMarkingToGluedCubic E s := by
  apply Scheme.Cover.hom_ext ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom)
  intro i
  exact (hf i).trans (smoothMarkingToGluedCubic_chart E s i).symm

end FLT.Mazur.GeneralizedEllipticCurve
