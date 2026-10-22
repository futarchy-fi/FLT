/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicPreimages
public import FLT.Mazur.ModuleSectionRatioAlongMorphism

/-!
# The original marking evaluated on the Y generator chart

Lift the actual marking to the original Y generator open and evaluate its
section ratios in the retained tensor frame. Both the scalar map and all three
coordinates are computed over the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingMarkingRatiosProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "B" => Scheme.Opens.topIso (X := E.curve.left) (U)

/-- The original marking factors through the Y generator open. -/
def smoothMarkingMarkingY : S ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (t).left (by
    rw [Scheme.Opens.range_ι]
    exact sectionPoleGenerator_contains_marking (t).left (hI) e 3 (T 1)
      (smoothMarkingProjectiveY_coefficient E s e))

/-- This lift is the original marking after the actual open inclusion. -/
@[reassoc] theorem smoothMarkingMarkingY_ι :
    smoothMarkingMarkingY E s e ≫ (U).ι = (t).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual normalized ratios on the Y chart evaluate to [0, 1, 0]. -/
theorem smoothMarkingMarkingY_ratio (i : Fin 3) :
    (smoothMarkingMarkingY E s e).appTop
      ((B).inv (sectionRatioOn (tensorPower (L) 3) (T 1) (U) le_rfl (T i))) =
        (![0, 1, 0] : Fin 3 → Γ(S, ⊤)) i := by
  erw [openFactor_appTop (t).left (U)
    (smoothMarkingMarking_preimage_yGenerator E s e).ge
    _ (smoothMarkingMarkingY_ι E s e)]
  have h := sectionRatioOn_frame (t).left (tensorPower (L) 3) (U)
    (smoothMarkingMarking_preimage_yGenerator E s e).ge (T 1) (T i) le_rfl
    (sectionPoleMultiplicativeFrame (t).left (hI) e 3)
    (smoothMarkingProjectiveY_coefficient E s e)
  exact h.trans (smoothMarkingProjectiveSections_coefficient E s e i)

/-- The actual chart scalar map restricts to the identity along the original marking. -/
theorem smoothMarkingMarkingY_scalar (a : Γ(S, ⊤)) :
    (smoothMarkingMarkingY E s e).appTop
      ((B).inv (sectionChartScalars E.curve.hom.appTop.hom (U) a)) = a := by
  erw [openFactor_appTop (t).left (U)
    (smoothMarkingMarking_preimage_yGenerator E s e).ge
    _ (smoothMarkingMarkingY_ι E s e)]
  unfold sectionChartScalars
  change (t).left.appLE (U) ⊤ _ (E.curve.left.presheaf.map _ (E.curve.hom.appTop a)) = a
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_eq_app]
  change ((t).left ≫ E.curve.hom).appTop a = a
  rw [(t).w]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
