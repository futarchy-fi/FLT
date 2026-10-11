/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingFamily
public import FLT.Mazur.WeierstrassCoefficientZero

/-!
# Coefficient change of the pointed one-gon smoothing

The actual integral cubic comparison is cartesian and retains the infinity
section for every coefficient algebra, including singular specializations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (t : R)

/-- Equation transport preserves the actual structure morphism. -/
@[reassoc] theorem equationTransport_structure {U V : WeierstrassCurve S} (h : U = V) :
    eqToHom (congrArg integralCurve h) ≫ integralCurveStructure V =
      integralCurveStructure U := by
  subst V
  simp

/-- Equation transport preserves the actual infinity point. -/
@[reassoc] theorem equationTransport_zero {U V : WeierstrassCurve S} (h : U = V) :
    integralCurveZero U ≫ eqToHom (congrArg integralCurve h) = integralCurveZero V := by
  subst V
  simp

/-- The original coefficient comparison, transported along the explicit equation identity. -/
def coefficientMorphism : (family (algebraMap R S t)).left ⟶ (family t).left :=
  eqToHom (congrArg integralCurve (equation_map t (algebraMap R S)).symm) ≫
    integralCoefficientMorphism (equation t)

/-- The actual square for the specified smoothing parameter is cartesian. -/
theorem coefficient_isPullback :
    IsPullback (coefficientMorphism (S := S) t) (family (algebraMap R S t)).hom
      (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have h := integralCoefficient_isPullback (S := S) (equation t)
  refine h.of_iso (eqToIso (congrArg integralCurve (equation_map t (algebraMap R S))))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp [family]) (by simp)
  · simp [coefficientMorphism]
  · simpa [family] using
      (equationTransport_structure (equation_map t (algebraMap R S))).symm

/-- The original coefficient comparison preserves the infinity marking. -/
@[reassoc] theorem marking_coefficientMorphism :
    marking (algebraMap R S t) ≫ coefficientMorphism t =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ marking t := by
  change integralCurveZero _ ≫
    eqToHom (congrArg integralCurve (equation_map t (algebraMap R S)).symm) ≫
      integralCoefficientMorphism (equation t) = _
  rw [equationTransport_zero_assoc (equation_map t (algebraMap R S)).symm]
  exact integralCoefficientMorphism_zero (S := S) (equation t)

/-- The family with extended coefficients is the actual pullback of the original family. -/
def coefficientPullbackIso : (family (algebraMap R S t)).left ≅
    pullback (family t).hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (coefficient_isPullback t).isoPullback

/-- The comparison retains the original curve projection. -/
@[reassoc] theorem coefficientPullbackIso_fst :
    (coefficientPullbackIso (S := S) t).hom ≫ pullback.fst _ _ = coefficientMorphism t :=
  (coefficient_isPullback t).isoPullback_hom_fst

/-- The comparison retains the actual coefficient projection. -/
@[reassoc] theorem coefficientPullbackIso_snd :
    (coefficientPullbackIso (S := S) t).hom ≫ pullback.snd _ _ =
      (family (algebraMap R S t)).hom :=
  (coefficient_isPullback t).isoPullback_hom_snd

end FLT.Mazur.OneGonSmoothing
