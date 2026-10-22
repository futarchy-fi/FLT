/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChangeCubic
public import FLT.Mazur.WeierstrassIntegralBaseChange

/-!
# The independently recomputed cubic is the actual categorical pullback

Compose the full pointed coordinate change with the cartesian coefficient
comparison. Both projections retain the original morphisms explicitly.
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
/-- The new equation's complete cubic is the categorical pullback of the original cubic. -/
def smoothMarkingCubicPullbackIso :
    integralCurve (V) ≅ Limits.pullback (integralCurveStructure (W)) (Spec.map g.appTop) := by
  let _ := g.appTop.hom.toAlgebra
  exact smoothMarkingBaseChangeCubicIso E g s a b ≪≫ integralCurveCoefficientBaseChangeIso (W)

/-- The first projection is the full coordinate comparison followed by coefficient projection. -/
@[reassoc] theorem smoothMarkingCubicPullbackIso_fst :
    let _ := g.appTop.hom.toAlgebra
    (smoothMarkingCubicPullbackIso E g s a b).hom ≫ Limits.pullback.fst _ _ =
      (smoothMarkingBaseChangeCubicIso E g s a b).hom ≫ integralCoefficientMorphism (W) := by
  let _ := g.appTop.hom.toAlgebra
  change ((smoothMarkingBaseChangeCubicIso E g s a b).hom ≫
    (integralCurveCoefficientBaseChangeIso (W)).hom) ≫ Limits.pullback.fst _ _ = _
  rw [Category.assoc, integralCurveCoefficientBaseChangeIso_fst]

/-- The second projection is precisely the independently constructed cubic's structure map. -/
@[reassoc] theorem smoothMarkingCubicPullbackIso_snd :
    (smoothMarkingCubicPullbackIso E g s a b).hom ≫ Limits.pullback.snd _ _ =
      integralCurveStructure (V) := by
  let _ := g.appTop.hom.toAlgebra
  change ((smoothMarkingBaseChangeCubicIso E g s a b).hom ≫
    (integralCurveCoefficientBaseChangeIso (W)).hom) ≫ Limits.pullback.snd _ _ = _
  rw [Category.assoc, integralCurveCoefficientBaseChangeIso_snd]
  exact smoothMarkingBaseChangeCubicIso_over E g s a b

end FLT.Mazur.GeneralizedEllipticCurve
