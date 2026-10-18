/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangeEquationLocus
public import FLT.Mazur.WeierstrassCoefficientGroup
public import FLT.Mazur.WeierstrassVariableChangeGroup
public import FLT.Mazur.WeierstrassGeneralizedSmoothComparison
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# The varying comparison of the original generalized elliptic curves

The universal admissible change compares the actual coefficient pullbacks
of the two smooth generalized elliptic models. The comparison retains the
original curve, group, and action, so full subgroup conditions can be imposed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
  {A : Type} [CommRing A] [Algebra R A]
  (C : VariableChange A) (h : C • V.map (algebraMap R A) = W.map (algebraMap R A))

/-- Smoothness of the original model survives every coefficient base change. -/
theorem modelBaseChange_smooth : Smooth
    ((integralGeneralizedEllipticCurve W hW).baseChange (Spec.algebraMap R A)).curve.hom := by
  let _ := integralCurveStructure_smooth W hW
  change Smooth (Limits.pullback.snd (integralCurveStructure W) (Spec.algebraMap R A))
  infer_instance

/-- The comparison as an isomorphism of the actual bundled coefficient pullback groups. -/
def changeCoefficientGroupIso :
    (Over.pullback (Spec.algebraMap R A)).mapCommGrp.obj (integralCurveGroup W hW) ≅
      (Over.pullback (Spec.algebraMap R A)).mapCommGrp.obj (integralCurveGroup V hV) :=
  (integralCurveCoefficientGroupIso W hW (by rw [map_Δ]; exact hW.map _)).symm ≪≫
    integralVariableChangeGroupIso _ _ C h
      (by rw [map_Δ]; exact hV.map _) (by rw [map_Δ]; exact hW.map _) ≪≫
    integralCurveCoefficientGroupIso V hV (by rw [map_Δ]; exact hV.map _)

/-- The actual original smooth groups compare through the coefficient and variable-change maps. -/
def changeBaseGroupIso :
    ((integralGeneralizedEllipticCurve W hW).baseChange (Spec.algebraMap R A)).group ≅
      ((integralGeneralizedEllipticCurve V hV).baseChange (Spec.algebraMap R A)).group :=
  (CommGrp.forget (Over (Spec (.of A)))).mapIso (changeCoefficientGroupIso W V hW hV C h)

instance changeBaseGroupIso_isMonHom : IsMonHom (changeBaseGroupIso W V hW hV C h).hom := by
  change IsMonHom (changeCoefficientGroupIso W V hW hV C h).hom.hom.hom.hom
  infer_instance

/-- Each compatible change gives a full comparison of the original base-changed DR models. -/
def changeBaseGeneralizedIso :
    (integralGeneralizedEllipticCurve W hW).baseChange (Spec.algebraMap R A) ≅
      (integralGeneralizedEllipticCurve V hV).baseChange (Spec.algebraMap R A) := by
  let _ := modelBaseChange_smooth W hW (A := A)
  let _ := modelBaseChange_smooth V hV (A := A)
  exact isoOfSmoothGroup _ _ (changeBaseGroupIso W V hW hV C h)

/-- The full extension keeps precisely the constructed comparison of the original groups. -/
theorem changeBaseGeneralizedIso_group :
    (changeBaseGeneralizedIso W V hW hV C h).hom.group =
      (changeBaseGroupIso W V hW hV C h).hom := rfl

/-- The constructed comparison parameter carries a universal full generalized-curve comparison. -/
def universalGeneralizedComparison :
    (integralGeneralizedEllipticCurve W hW).baseChange
      (Spec.algebraMap R (EquationRing W V)) ≅
    (integralGeneralizedEllipticCurve V hV).baseChange
      (Spec.algebraMap R (EquationRing W V)) :=
  changeBaseGeneralizedIso W V hW hV (equationChange W V) (equationChange_equation W V)

end FLT.Mazur.WeierstrassChangeParameter
