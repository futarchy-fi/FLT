/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingGluedProper

/-!
# Cartesian recovery of the original whole-curve morphisms

The affine-frame cubic map is the actual restriction of the global map.
The proof cancels the already constructed cubic/base pullback square from
the original whole-family base-change square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

local instance gluedCartesianNoetherian (i : SmoothMarkingAffineChart E s) :
    IsNoetherianRing Γ(i.base.1.toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The original affine-frame whole-curve map, with its original chart as target. -/
def smoothMarkingAffineMorphism (i : SmoothMarkingAffineChart E s) :
    (E.baseChange i.base.1.ι).curve.left ⟶ (smoothMarkingAffineDiagram E s).obj i :=
  smoothMarkingToIntegralCubic (E.baseChange i.base.1.ι) (pullSection i.base.1.ι s) i.frame

/-- The local whole-curve morphism retains its original affine base. -/
@[reassoc] theorem smoothMarkingAffineMorphism_over (i : SmoothMarkingAffineChart E s) :
    smoothMarkingAffineMorphism E s i ≫ smoothMarkingAffineStructure E s i =
      Limits.pullback.snd E.curve.hom i.base.1.ι := by
  unfold smoothMarkingAffineMorphism smoothMarkingAffineStructure smoothMarkingAffineEquation
  rw [← Category.assoc, smoothMarkingToIntegralCubic_over, Category.assoc]
  change (E.baseChange i.base.1.ι).curve.hom ≫
    i.base.1.toScheme.isoSpec.hom ≫ i.base.1.toScheme.isoSpec.inv = _
  rw [Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The square between the actual original local and global curve maps commutes. -/
@[reassoc] theorem smoothMarkingAffineMorphism_chart (i : SmoothMarkingAffineChart E s) :
    smoothMarkingAffineMorphism E s i ≫ smoothMarkingGluedChart E s i =
      Limits.pullback.fst E.curve.hom i.base.1.ι ≫ smoothMarkingToGluedCubic E s :=
  (smoothMarkingToGluedCubic_chart E s i).symm

/-- The entire original local curve is the categorical restriction of the global curve map. -/
theorem smoothMarkingAffineMorphism_isPullback (i : SmoothMarkingAffineChart E s) :
    IsPullback (smoothMarkingAffineMorphism E s i)
      (Limits.pullback.fst E.curve.hom i.base.1.ι)
      (smoothMarkingGluedChart E s i) (smoothMarkingToGluedCubic E s) := by
  have h : IsPullback
      (smoothMarkingAffineMorphism E s i ≫ smoothMarkingAffineStructure E s i)
      (Limits.pullback.fst E.curve.hom i.base.1.ι) i.base.1.ι
      (smoothMarkingToGluedCubic E s ≫ smoothMarkingGluedBase E s) := by
    rw [smoothMarkingAffineMorphism_over, smoothMarkingToGluedCubic_over]
    exact (IsPullback.of_hasPullback E.curve.hom i.base.1.ι).flip
  exact h.of_right (smoothMarkingAffineMorphism_chart E s i)
    (smoothMarkingGluedChart_isPullback E s i)

/-- The canonical categorical pullback is isomorphic to the original local whole curve. -/
def smoothMarkingAffineMorphismPullbackIso (i : SmoothMarkingAffineChart E s) :
    (E.baseChange i.base.1.ι).curve.left ≅
      Limits.pullback (smoothMarkingGluedChart E s i) (smoothMarkingToGluedCubic E s) :=
  (smoothMarkingAffineMorphism_isPullback E s i).isoPullback

/-- The comparison recovers the original local cubic map exactly. -/
@[reassoc] theorem smoothMarkingAffineMorphismPullbackIso_fst
    (i : SmoothMarkingAffineChart E s) :
    (smoothMarkingAffineMorphismPullbackIso E s i).hom ≫ Limits.pullback.fst _ _ =
      smoothMarkingAffineMorphism E s i := IsPullback.isoPullback_hom_fst _

/-- The comparison also retains the original whole-family projection. -/
@[reassoc] theorem smoothMarkingAffineMorphismPullbackIso_snd
    (i : SmoothMarkingAffineChart E s) :
    (smoothMarkingAffineMorphismPullbackIso E s i).hom ≫ Limits.pullback.snd _ _ =
      Limits.pullback.fst E.curve.hom i.base.1.ι := IsPullback.isoPullback_hom_snd _

end FLT.Mazur.GeneralizedEllipticCurve
