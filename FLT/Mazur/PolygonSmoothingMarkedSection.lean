/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Unit-marked sections in the arithmetic smoothing charts

Each coefficient unit a gives an actual section (a,t/a). The section factors
through the specified first Laurent open, whose structure morphism is smooth.
The coordinate one gives a distinguished section for every smoothing parameter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R]

/-- The chart point with first coordinate a and second coordinate t/a. -/
def markedEvaluation (t : R) (a : Rˣ) : ChartRing t →ₐ[R] R :=
  evaluate t (a : R) (t * ↑a⁻¹) (by
    rw [mul_left_comm, Units.mul_inv, mul_one]
    rfl)

/-- The marking retains its specified unit coordinate. -/
@[simp] theorem markedEvaluation_left (t : R) (a : Rˣ) :
    markedEvaluation t a (leftCoordinate t) = (a : R) := evaluate_left ..

/-- The second marking coordinate is exactly t/a. -/
@[simp] theorem markedEvaluation_right (t : R) (a : Rˣ) :
    markedEvaluation t a (rightCoordinate t) = t * ↑a⁻¹ := evaluate_right ..

/-- The marked evaluation is the restriction of the original Laurent unit point. -/
theorem markedEvaluation_laurent (t : R) (a : Rˣ) :
    (LaurentUnitPoints.evalUnit a).comp (leftLaurentMap t) = markedEvaluation t a := by
  apply chartRing_hom_ext t <;> simp

/-- The actual unit section of the coefficient torus. -/
def markedTorusSection (a : Rˣ) : Spec (.of R) ⟶ branchTorus R :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit a).toRingHom)

/-- The actual arithmetic marked section of the smoothing chart. -/
def markedSection (t : R) (a : Rˣ) : Spec (.of R) ⟶ chart R t :=
  Spec.map (CommRingCat.ofHom (markedEvaluation t a).toRingHom)

/-- Each marking is a section of the original arithmetic structure morphism. -/
@[reassoc] theorem markedSection_base (t : R) (a : Rˣ) :
    markedSection t a ≫ chartStructure R t = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (markedEvaluation t a).comp_algebraMap

/-- The marked section factors through the actual first punctured branch. -/
@[reassoc] theorem markedTorusSection_left (t : R) (a : Rˣ) :
    markedTorusSection a ≫ leftBranchOpen R t = markedSection t a := by
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change LaurentUnitPoints.evalUnit a
    (leftPunctureToLaurent t (algebraMap (ChartRing t) _ z)) = markedEvaluation t a z
  rw [leftPunctureToLaurent_map]
  exact DFunLike.congr_fun (markedEvaluation_laurent t a) z

/-- The first punctured branch has a smooth structure morphism over the arithmetic base. -/
instance leftBranchOpen_smooth (t : R) : Smooth (leftBranchOpen R t ≫ chartStructure R t) := by
  rw [leftBranchOpen_base]
  exact MultiplicativeGroupScheme.smooth R

/-- The second punctured branch also has a smooth structure morphism. -/
instance rightBranchOpen_smooth (t : R) :
    Smooth (rightBranchOpen R t ≫ chartStructure R t) := by
  rw [rightBranchOpen_base]
  exact MultiplicativeGroupScheme.smooth R

/-- The zero-parameter marking lies on the original first coordinate axis. -/
theorem markedEvaluation_zero_right (a : Rˣ) :
    markedEvaluation (0 : R) a (rightCoordinate 0) = 0 := by
  rw [markedEvaluation_right, zero_mul]

end FLT.Mazur.PolygonSmoothing
