/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicPullback
public import FLT.Mazur.GeneralizedCurveMarkingBaseChangeMorphism

/-!
# The original curve morphism into the categorical cubic pullback

The independently recomputed map, followed by the constructed cubic pullback
isomorphism, equals the canonical lift of the original map and new base map.
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
local notation "C" => smoothMarkingBaseChangeChange E g s a b
local notation "hC" => And.left (And.right (smoothMarkingBaseChangeChange_spec E g s a b))
omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The original map and changed structure morphism commute over the coefficient spectrum. -/
theorem smoothMarkingCubicPullback_square :
    (Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToIntegralCubic E s a) ≫
        integralCurveStructure (W) =
      ((E.baseChange g).curve.hom ≫ T.toSpecΓ) ≫ Spec.map g.appTop := by
  rw [Category.assoc, smoothMarkingToIntegralCubic_over,
    ← Category.assoc, (smoothMarkingBaseChange_cartesian E g).w,
    Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc]

/-- The actual map from the changed original curve to the categorical pulled-back cubic. -/
def smoothMarkingToCubicPullback :
    (E.baseChange g).curve.left ⟶
      Limits.pullback (integralCurveStructure (W)) (Spec.map g.appTop) :=
  Limits.pullback.lift
    (Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToIntegralCubic E s a)
    ((E.baseChange g).curve.hom ≫ T.toSpecΓ) (smoothMarkingCubicPullback_square E g s a)

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The first projection retains the original whole-curve map, not just its affine functions. -/
@[reassoc] theorem smoothMarkingToCubicPullback_fst :
    smoothMarkingToCubicPullback E g s a ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToIntegralCubic E s a :=
  Limits.pullback.lift_fst _ _ _

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The second projection retains the actual changed family's base map. -/
@[reassoc] theorem smoothMarkingToCubicPullback_snd :
    smoothMarkingToCubicPullback E g s a ≫ Limits.pullback.snd _ _ =
      (E.baseChange g).curve.hom ≫ T.toSpecΓ :=
  Limits.pullback.lift_snd _ _ _

/-- Recomputing the cubic map agrees with the categorical base change of the original map. -/
theorem smoothMarkingToIntegralCubic_pullback :
    smoothMarkingToIntegralCubic (E.baseChange g) (pullSection g s) b ≫
      (smoothMarkingCubicPullbackIso E g s a b).hom = smoothMarkingToCubicPullback E g s a := by
  let _ := g.appTop.hom.toAlgebra
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, smoothMarkingCubicPullbackIso_fst,
      smoothMarkingToIntegralCubic_baseChange, smoothMarkingToCubicPullback_fst]
  · rw [Category.assoc, smoothMarkingCubicPullbackIso_snd,
      smoothMarkingToIntegralCubic_over, smoothMarkingToCubicPullback_snd]

end FLT.Mazur.GeneralizedEllipticCurve
