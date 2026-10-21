/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCommonCoefficientCurve
public import FLT.Mazur.OneGonCommonCoefficientGroup

/-!
# Independent smooth comparisons retain the entire cubic inclusion

The common-base smooth group isomorphism and the common-base whole-curve
isomorphism commute with the actual open immersions. Thus comparison of a
smooth subgroup will also compare its full whole-cubic embedding.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]

/-- The intrinsic smooth group includes in the whole one-gon over the same base. -/
def smoothCurveInclusion (a : A) : (integralSmoothGroup (equation a)).X ⟶ family a :=
  Over.homMk (integralSmoothOpen (equation a)).ι rfl

/-- The sealed relative curve comparison retains the original geometric projection. -/
@[reassoc] theorem coefficientCurveOverIso_fst [Algebra A C] (a : A) :
    (coefficientCurveOverIso (C := C) a).hom.left ≫
      pullback.fst (family a).hom (Spec.map (CommRingCat.ofHom (algebraMap A C))) =
        coefficientMorphism a := by
  rw [coefficientCurveOverIso_def]
  exact coefficientPullbackIso_fst a

/-- Both coefficient comparisons preserve the actual smooth-open inclusion. -/
theorem coefficientSmoothCurveInclusion [Algebra A C] (a : A) :
    (smoothCoefficientGroupOverIso (S := C) a).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).map
        (smoothCurveInclusion a) =
      smoothCurveInclusion (algebraMap A C a) ≫ (coefficientCurveOverIso a).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [coefficientCurveOverIso_fst, ← Category.assoc]
    erw [smoothCoefficientGroupIso_fst]
    exact smoothCoefficientProjection_inclusion a
  · exact (Over.w _).trans (Over.w _).symm

/-- Equality transport on parameters preserves the full smooth-open inclusion. -/
theorem parameterTransport_smoothCurveInclusion {s t : C} (h : s = t) :
    ((CommGrp.forget (Over (Spec (.of C)))).mapIso
      (smoothEquationGroupIso (congrArg equation h))).hom ≫ smoothCurveInclusion t =
        smoothCurveInclusion s ≫ (parameterCurveIso h).hom := by
  subst t
  rw [smoothEquationGroupIso_def, parameterCurveIso_def]
  simp

/-- Independent coefficient models have the same full smooth inclusion after comparison. -/
theorem commonCoefficientIso_inclusion [Algebra A C] [Algebra B C]
    (a : A) (b : B) (h : algebraMap A C a = algebraMap B C b) :
    (commonCoefficientSmoothIso a b h).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B C)))).map
        (smoothCurveInclusion b) =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).map
        (smoothCurveInclusion a) ≫ (commonCoefficientCurveIso a b h).hom := by
  apply (cancel_epi (smoothCoefficientGroupOverIso a).hom).mp
  rw [← Category.assoc, commonCoefficientSmoothIso_recovery, Category.assoc,
    coefficientSmoothCurveInclusion, ← Category.assoc,
    parameterTransport_smoothCurveInclusion, Category.assoc, ← commonCoefficientCurveIso_recovery,
    ← Category.assoc, ← coefficientSmoothCurveInclusion, Category.assoc]

end FLT.Mazur.OneGonSmoothing
