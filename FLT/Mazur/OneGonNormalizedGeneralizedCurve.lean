/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentPointedPresentation
public import FLT.Mazur.WeierstrassVariableChangeWholeAction
public import FLT.Mazur.ArithmeticOneGonGeneralizedCurve
public import FLT.Mazur.GeneralizedCurveGeometricRotationsIso
public import FLT.Mazur.ClassifiedGenusOneCartesian
public import FLT.Mazur.GeneralizedCurveBaseChangeIso

/-!
# Full generalized curves on original nodal Weierstrass deformations

An actual admissible normal form supplies the geometric family and rotations.
The group and whole action are the independently constructed operations on the
original cubic. The resulting comparison is an isomorphism of full DR objects.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
open OneGonSmoothing WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (t : R) (C : VariableChange R) (h : C • W = equation t) (ht : IsUnit (1 + 432 * t))

/-- The original cubic with its intrinsic operations, justified by its actual normal form. -/
def curveOfNormalForm : GeneralizedEllipticCurve (Spec (.of R)) where
  curve := integralCurveOver W
  family := (ArithmeticOneGonFamily.classifiedGenusOneFamily t ht).of_overIso
    (integralVariableChangeOverIso W (equation t) C h)
  group := (integralSmoothGroup W).X
  smoothIso := Iso.refl _
  act := integralSmoothWholeAction W
  unit_act := integralSmoothWholeAction_unit W
  assoc_act := integralSmoothWholeAction_assoc W
  restriction := by
    change (integralSmoothGroup W).X ◁
      (𝟙 _ ≫ integralSmoothWholeInclusion W) ≫ integralSmoothWholeAction W = _
    rw [Category.id_comp]
    exact integralSmoothWholeAction_restriction W
  rotations := by
    let _ : LocallyOfFinitePresentation (integralCurveOver W).hom :=
      integralCurveStructure_finitePresentation W
    let _ : LocallyOfFinitePresentation (Over.mk (integralCurveStructure (equation t))).hom :=
      integralCurveStructure_finitePresentation (equation t)
    exact GeneralizedCurveGraph.geometricRotations_of_iso
      (integralVariableChangeOverIso W (equation t) C h)
      (integralVariableChangeSmoothOverIso W (equation t) C h)
      _ _ (integralVariableChangeOverIso_wholeAction W (equation t) C h)
      (ArithmeticOneGonRotations.wholeAction_geometricRotations t ht)

/-- The generalized deformation has exactly the original proper cubic. -/
theorem curveOfNormalForm_curve :
    (curveOfNormalForm W t C h ht).curve = integralCurveOver W := rfl

/-- The group is the independently constructed intrinsic smooth group of the original cubic. -/
theorem curveOfNormalForm_group :
    (curveOfNormalForm W t C h ht).group = (integralSmoothGroup W).X := rfl

/-- The whole action is the independently constructed original smooth-by-whole addition. -/
theorem curveOfNormalForm_action :
    (curveOfNormalForm W t C h ht).act = integralSmoothWholeAction W := rfl

/-- The generalized inclusion is the original smooth-open inclusion. -/
theorem curveOfNormalForm_inclusion :
    (curveOfNormalForm W t C h ht).inclusion = integralSmoothWholeInclusion W := by
  change 𝟙 _ ≫ integralSmoothWholeInclusion W = _
  exact Category.id_comp _

/-- Normalization identifies the entire generalized curve, including its group and action. -/
@[irreducible] def generalizedNormalFormIso :
    ArithmeticOneGonGeneralizedCurve.curve t ht ≅ curveOfNormalForm W t C h ht := by
  let g : (ArithmeticOneGonGeneralizedCurve.curve t ht).group ≅
      (curveOfNormalForm W t C h ht).group :=
    (CommGrp.forget (Over (Spec (.of R)))).mapIso
      (integralVariableChangeIntrinsicGroupIso W (equation t) C h)
  let _ : IsMonHom g.hom := by
    change IsMonHom (integralVariableChangeIntrinsicGroupIso W (equation t) C h).hom.hom.hom.hom
    infer_instance
  exact isoMk (integralVariableChangeOverIso W (equation t) C h) g
    (by
      rw [ArithmeticOneGonGeneralizedCurve.curve_inclusion, curveOfNormalForm_inclusion]
      apply Over.OverMorphism.ext
      exact (integralVariableChangeSmoothMap_inclusion W (equation t) C h).symm)
    (integralVariableChangeOverIso_wholeAction W (equation t) C h)

/-- The full comparison retains the original proper admissible map. -/
theorem generalizedNormalFormIso_curve :
    (generalizedNormalFormIso W t C h ht).hom.curve =
      (integralVariableChangeOverIso W (equation t) C h).hom := by
  unfold generalizedNormalFormIso
  rfl

/-- The full comparison retains the independently proved intrinsic group map. -/
theorem generalizedNormalFormIso_group :
    (generalizedNormalFormIso W t C h ht).hom.group.left =
      integralVariableChangeSmoothMap W (equation t) C h := by
  unfold generalizedNormalFormIso
  rfl

end FLT.Mazur.OneGonInfinitesimal
