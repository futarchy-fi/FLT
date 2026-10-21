/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCommonCoefficientInclusion
public import FLT.Mazur.WeierstrassSmoothWholeCoefficientAction
public import FLT.Mazur.WeierstrassSmoothWholeEquationTransport

/-!
# Coefficient equivariance of the arithmetic one-gon action

The actual one-gon comparison preserves the whole action, including singular
second inputs, after the specified equality transport of its equation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)
local notation "F" => Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
local notation "h" => Eq.symm (equation_map t (algebraMap R S))

/-- The sealed one-gon curve comparison is the transported original coefficient comparison. -/
theorem coefficientCurveOverIso_transport :
    (coefficientCurveOverIso (C := S) t).hom =
      (equationCurveOverIso h).hom ≫
        (integralCurveCoefficientOverIso (S := S) (equation t)).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hf := integralCurveCoefficientOverIso_fst (S := S) (equation t)
    change (integralCurveCoefficientOverIso (S := S) (equation t)).hom.left ≫
      pullback.fst (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        integralCoefficientMorphism (equation t) at hf
    rw [coefficientCurveOverIso_fst, Over.comp_left, Category.assoc, hf,
      equationCurveOverIso_hom_left]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

/-- The smooth comparison uses the same equation transport as the whole curve. -/
theorem smoothCoefficientGroupOverIso_transport :
    (smoothCoefficientGroupOverIso (S := S) t).hom =
      ((CommGrp.forget (Over (Spec (.of S)))).mapIso
        (smoothEquationGroupIso h)).hom ≫
          (originalSmoothCoefficientOverIso S (equation t)).hom := by
  unfold smoothCoefficientGroupOverIso
  rw [smoothCoefficientGroupIso_def]
  rfl

/-- The one-gon coefficient isomorphisms preserve the full smooth-by-whole action. -/
theorem coefficientSmoothWholeAction :
    integralSmoothWholeAction (equation (algebraMap R S t)) ≫
      (coefficientCurveOverIso t).hom =
        ((smoothCoefficientGroupOverIso t).hom ⊗ₘ (coefficientCurveOverIso t).hom) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ (F).map (integralSmoothWholeAction (equation t)) := by
  rw [coefficientCurveOverIso_transport, smoothCoefficientGroupOverIso_transport,
    ← Category.assoc, equationCurveOverIso_action, Category.assoc,
    originalSmoothWholeCoefficientIso_action]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, family, integralCurveOver]

end FLT.Mazur.OneGonSmoothing
