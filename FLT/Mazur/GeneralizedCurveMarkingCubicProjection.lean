/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicPullbackMorphism

/-!
# Cubic projection to the original framed family

The categorical pullback comparison gives a concrete morphism between the
independently recomputed cubic and the original cubic. It retains the base
map and commutes with the actual whole-curve cubic construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingWeierstrassCurve smoothMarkingTransportedLift
  smoothMarkingTransportedFrame smoothMarkingBaseChangeChange
variable {S T : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback (pullSection g s ≫ (E.baseChange g).inclusion).left).obj
    (divisorLineBundle (pullSection g s ≫ (E.baseChange g).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1) ≅ structureModule T)
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "V" => smoothMarkingWeierstrassCurve (E.baseChange g) (pullSection g s) b

/-- The complete cubic projection for an arbitrary independently framed base change. -/
def smoothMarkingCubicProjection : integralCurve (V) ⟶ integralCurve (W) :=
  (smoothMarkingCubicPullbackIso E g s a b).hom ≫ Limits.pullback.fst _ _

/-- The projection retains the original map of coefficient spectra. -/
@[reassoc] theorem smoothMarkingCubicProjection_over :
    smoothMarkingCubicProjection E g s a b ≫ integralCurveStructure (W) =
      integralCurveStructure (V) ≫ Spec.map g.appTop := by
  rw [smoothMarkingCubicProjection, Category.assoc, Limits.pullback.condition,
    ← Category.assoc, smoothMarkingCubicPullbackIso_snd]

/-- The projection commutes with the actual original whole-curve morphism. -/
@[reassoc] theorem smoothMarkingToIntegralCubic_projection :
    smoothMarkingToIntegralCubic (E.baseChange g) (pullSection g s) b ≫
      smoothMarkingCubicProjection E g s a b =
        Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToIntegralCubic E s a := by
  rw [smoothMarkingCubicProjection,
    ← Category.assoc (smoothMarkingToIntegralCubic (E.baseChange g) (pullSection g s) b),
    smoothMarkingToIntegralCubic_pullback, smoothMarkingToCubicPullback_fst]

end FLT.Mazur.GeneralizedEllipticCurve
