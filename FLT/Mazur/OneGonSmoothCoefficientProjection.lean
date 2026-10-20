/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingCoefficientChange
public import FLT.Mazur.OneGonSmoothEquationProjection
public import FLT.Mazur.WeierstrassSmoothCoefficientCartesian

/-!
# Smooth coefficient projection for the actual one-gon equation

The smooth coefficient morphism preserves the specified smoothing parameter
and the full cubic inclusion. No invertibility of the parameter is required.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart WeierstrassDividedDepth

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)

/-- The actual smooth coefficient map, transported along the one-gon equation identity. -/
def smoothCoefficientProjection :
    (integralSmoothOpen (equation (algebraMap R S t))).toScheme ⟶
      (integralSmoothOpen (equation t)).toScheme :=
  eqToHom (congrArg (fun W => (integralSmoothOpen W).toScheme)
    (equation_map t (algebraMap R S)).symm) ≫
      originalSmoothCoefficientMap S (equation t)

/-- The projection retains the whole-cubic coefficient morphism. -/
@[reassoc] theorem smoothCoefficientProjection_inclusion :
    smoothCoefficientProjection (S := S) t ≫ (integralSmoothOpen (equation t)).ι =
      (integralSmoothOpen (equation (algebraMap R S t))).ι ≫ coefficientMorphism t := by
  rw [smoothCoefficientProjection, Category.assoc, originalSmoothCoefficientMap_inclusion,
    smoothEquationTransport_inclusion_assoc (equation_map t (algebraMap R S)).symm]
  rfl

/-- The projection retains the actual base map. -/
@[reassoc] theorem smoothCoefficientProjection_structure :
    smoothCoefficientProjection (S := S) t ≫ integralSmoothStructure (equation t) =
      integralSmoothStructure (equation (algebraMap R S t)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change _ ≫ (integralSmoothOpen (equation t)).ι ≫ _ = _
  rw [smoothCoefficientProjection_inclusion_assoc]
  have h := (coefficient_isPullback (S := S) t).w
  change coefficientMorphism t ≫ integralCurveStructure (equation t) = _ at h
  rw [h]
  rfl

/-- Smooth equation transport is Cartesian over the two full smooth inclusions. -/
theorem smoothCoefficientProjection_inclusion_isPullback :
    IsPullback (smoothCoefficientProjection (S := S) t)
      (integralSmoothOpen (equation (algebraMap R S t))).ι
      (integralSmoothOpen (equation t)).ι (coefficientMorphism t) := by
  have h := originalSmoothCoefficientMap_inclusion_isPullback S (equation t)
  refine h.of_iso
    (eqToIso (congrArg (fun W => (integralSmoothOpen W).toScheme)
      (equation_map t (algebraMap R S)))) (Iso.refl _)
    (eqToIso (congrArg integralCurve (equation_map t (algebraMap R S))))
    (Iso.refl _) ?_ ?_ (by simp) ?_
  · simp [smoothCoefficientProjection]
  · exact (smoothEquationTransport_inclusion (equation_map t (algebraMap R S))).symm
  · simp [coefficientMorphism]

/-- The original smooth model is recovered by the same Cartesian coefficient square. -/
theorem smoothCoefficientProjection_isPullback :
    IsPullback (smoothCoefficientProjection (S := S) t)
      (integralSmoothStructure (equation (algebraMap R S t)))
      (integralSmoothStructure (equation t))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (smoothCoefficientProjection_inclusion_isPullback t).paste_vert (coefficient_isPullback t)

end FLT.Mazur.OneGonSmoothing
