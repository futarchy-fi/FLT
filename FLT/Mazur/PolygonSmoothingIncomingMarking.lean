/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingMarkedIdeal
public import FLT.Mazur.PolygonSmoothingOverlapGraph

/-!
# The incoming marking in the full arithmetic chart

The inverse Laurent transition sends the marking with parameter a to
(ta,a⁻¹). Its full kernel is (y-a⁻¹), over the original coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R) (a : Rˣ)

/-- Evaluation at the actual incoming copy of the marked Laurent point. -/
def incomingMarkedEvaluation : ChartRing t →ₐ[R] R :=
  (markedEvaluation t a⁻¹).comp (branchSwapMap t)

/-- The incoming marking has the original first coordinate ta. -/
@[simp] theorem incomingMarkedEvaluation_left :
    incomingMarkedEvaluation t a (leftCoordinate t) = t * (a : R) := by
  simp [incomingMarkedEvaluation]

/-- The second coordinate retains the reciprocal of the specified marking parameter. -/
@[simp] theorem incomingMarkedEvaluation_right :
    incomingMarkedEvaluation t a (rightCoordinate t) = (a⁻¹ : Rˣ) := by
  simp [incomingMarkedEvaluation]

/-- The incoming evaluation is exactly restriction through the original Laurent overlap. -/
theorem incomingMarkedEvaluation_laurent :
    (LaurentUnitPoints.evalUnit a).comp (precedingLaurentMap R t) =
      incomingMarkedEvaluation t a := by
  apply chartRing_hom_ext t
  · simp [precedingLaurentMap, incomingMarkedEvaluation]
  · simp [precedingLaurentMap, incomingMarkedEvaluation]

/-- The entire incoming kernel is the principal right-coordinate marking ideal. -/
theorem incomingMarkedEvaluation_ker :
    RingHom.ker (incomingMarkedEvaluation t a).toRingHom =
      Ideal.span {rightCoordinate t - algebraMap R (ChartRing t) (a⁻¹ : Rˣ)} := by
  change (RingHom.ker (markedEvaluation t a⁻¹).toRingHom).comap
    (branchSwap t).toRingEquiv.symm = _
  rw [markedEvaluation_ker_eq, ← Ideal.map_comap_of_equiv (branchSwap t).toRingEquiv]
  rw [markedCoordinateIdeal, Ideal.map_span, Set.image_singleton]
  congr 2
  change branchSwapMap t (_ - _) = _
  rw [map_sub, branchSwapMap_left, AlgHom.commutes]

/-- The incoming section of the full arithmetic chart. -/
def incomingMarkedSection : Spec (.of R) ⟶ chart R t :=
  Spec.map (CommRingCat.ofHom (incomingMarkedEvaluation t a).toRingHom)

/-- The section uses the actual inverse-Laurent gluing map. -/
@[reassoc] theorem markedTorusSection_preceding :
    markedTorusSection a ≫ precedingBranch R t = incomingMarkedSection t a := by
  rw [precedingBranch_eq_spec, markedTorusSection, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (incomingMarkedEvaluation_laurent t a)

/-- At the original unit marking the full incoming ideal is (y-1). -/
theorem incomingMarkedEvaluation_one_ker :
    RingHom.ker (incomingMarkedEvaluation t 1).toRingHom =
      Ideal.span {rightCoordinate t - 1} := by
  rw [incomingMarkedEvaluation_ker]
  simp only [inv_one, Units.val_one, map_one]

end FLT.Mazur.PolygonSmoothing
