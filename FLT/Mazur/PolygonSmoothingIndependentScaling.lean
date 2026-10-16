/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingScalingBranches
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Independent branch scalings when the smoothing vanishes

Both coefficient units extend simultaneously over the entire nodal chart.
No relation between the units is needed when the actual parameter is zero.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R) (ht : t = 0)

/-- Independent coefficient scalings on the full zero-parameter chart. -/
def independentScale (a b : Rˣ) : ChartRing t →ₐ[R] ChartRing t :=
  evaluate t (algebraMap R _ a * leftCoordinate t)
    (algebraMap R _ b * rightCoordinate t) (by
      rw [mul_mul_mul_comm, coordinate_relation, ht, map_zero, mul_zero])

/-- The first coordinate retains its independently chosen coefficient. -/
@[simp] theorem independentScale_left (a b : Rˣ) :
    independentScale t ht a b (leftCoordinate t) =
      algebraMap R _ a * leftCoordinate t := evaluate_left ..

/-- The second coordinate retains its independently chosen coefficient. -/
@[simp] theorem independentScale_right (a b : Rˣ) :
    independentScale t ht a b (rightCoordinate t) =
      algebraMap R _ b * rightCoordinate t := evaluate_right ..

/-- The two identity coefficients fix every function on the chart. -/
@[simp] theorem independentScale_one :
    independentScale t ht 1 1 = AlgHom.id R (ChartRing t) := by
  apply chartRing_hom_ext t <;> simp

/-- Composition multiplies the two branch coefficients separately. -/
theorem independentScale_mul (a b c d : Rˣ) :
    independentScale t ht (a * c) (b * d) =
      (independentScale t ht a b).comp (independentScale t ht c d) := by
  apply chartRing_hom_ext t <;> simp [mul_left_comm, mul_comm]

/-- The constructed full-chart inverse uses the two inverse coefficients. -/
def independentScaleEquiv (a b : Rˣ) : ChartRing t ≃ₐ[R] ChartRing t :=
  { independentScale t ht a b with
    invFun := independentScale t ht a⁻¹ b⁻¹
    left_inv := fun x ↦ by
      have h := DFunLike.congr_fun (independentScale_mul t ht a⁻¹ b⁻¹ a b) x
      simpa using h.symm
    right_inv := fun x ↦ by
      have h := DFunLike.congr_fun (independentScale_mul t ht a b a⁻¹ b⁻¹) x
      simpa using h.symm }

/-- Independent scaling extends across the actual node, not only its punctures. -/
def independentScalingIso (a b : Rˣ) : chart R t ≅ chart R t :=
  Scheme.Spec.mapIso (independentScaleEquiv t ht a b).toRingEquiv.toCommRingCatIso.op

/-- Restriction to the first puncture uses precisely the first coefficient. -/
theorem leftLaurentMap_independentScale (a b : Rˣ) :
    (leftLaurentMap t).comp (independentScale t ht a b) =
      (PolygonScaledReciprocal.scaling a).comp (leftLaurentMap t) := by
  apply chartRing_hom_ext t <;>
    simp [PolygonScaledReciprocal.scaling, AlgHom.coe_mk, ht]

/-- Restriction to the second puncture uses precisely the second coefficient. -/
theorem rightLaurentMap_independentScale (a b : Rˣ) :
    ((leftLaurentMap t).comp (branchSwapMap t)).comp (independentScale t ht a b) =
      (PolygonScaledReciprocal.scaling b).comp
        ((leftLaurentMap t).comp (branchSwapMap t)) := by
  apply chartRing_hom_ext t <;>
    simp [PolygonScaledReciprocal.scaling, AlgHom.coe_mk, ht]

/-- The full first-branch square commutes with the constructed chart automorphism. -/
@[reassoc] theorem leftBranch_independentScaling (a b : Rˣ) :
    leftBranchOpen R t ≫ (independentScalingIso t ht a b).hom =
      (edgeScalingIso a).hom ≫ leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (leftLaurentMap_independentScale t ht a b)))

/-- The full second-branch square holds for the same chart automorphism. -/
@[reassoc] theorem rightBranch_independentScaling (a b : Rˣ) :
    rightBranchOpen R t ≫ (independentScalingIso t ht a b).hom =
      (edgeScalingIso b).hom ≫ rightBranchOpen R t := by
  rw [rightBranchOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (rightLaurentMap_independentScale t ht a b)))

/-- The simultaneous correction preserves the original coefficient structure. -/
@[reassoc] theorem independentScalingIso_base (a b : Rˣ) :
    (independentScalingIso t ht a b).hom ≫ chartStructure R t = chartStructure R t := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (independentScale t ht a b).comp_algebraMap)

end FLT.Mazur.PolygonSmoothing
