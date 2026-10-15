/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalUniversalEdges
public import FLT.Mazur.LaurentSchemeCoordinates

/-!
# The exact algebra map of universal Laurent edge scaling

The full scheme map is the spectrum of the explicit two-variable substitution.
Its invertible coordinate is the product of the two independent Laurent units.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R]

/-- The explicit coefficient algebra map of the universal full-edge action. -/
def universalEdgeAlgebra : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹][T;T⁻¹] where
  __ := PolygonUniversalScaling.overlapScale
  commutes' r := PolygonUniversalScaling.overlapScale_C r

/-- Universal scaling is exactly the spectrum of the original two-variable substitution. -/
theorem universalEdgeScaling_spec :
    universalEdgeScaling R = Spec.map (CommRingCat.ofHom (universalEdgeAlgebra R).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
    (PolygonScaledReciprocal.scaling (PolygonUniversalScaling.u (R := R))).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (PolygonScalingNaturality.coeffMap (LaurentPolynomial.C : R →+* R[T;T⁻¹]))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    simp [universalEdgeAlgebra, PolygonScaledReciprocal.scaling, CommRingCat.hom_comp]
  · simp [universalEdgeAlgebra, PolygonScaledReciprocal.scaling, CommRingCat.hom_comp]
  · simp [universalEdgeAlgebra, PolygonScaledReciprocal.scaling, CommRingCat.hom_comp]

/-- Universal edge scaling retains the full coefficient base. -/
@[reassoc] theorem universalEdgeScaling_base :
    universalEdgeScaling R ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹][T;T⁻¹])) := by
  rw [universalEdgeScaling_spec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (universalEdgeAlgebra R).comp_algebraMap

/-- The coordinate pulled back by scaling is the full product of independent Laurent units. -/
theorem universalEdgeAlgebra_coordinate :
    LaurentUnitPoints.pointUnit (universalEdgeAlgebra R) =
      Units.map (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹])
        (PolygonUniversalScaling.u (R := R)) * PolygonUniversalScaling.u := by
  apply Units.ext
  change PolygonUniversalScaling.overlapScale (LaurentPolynomial.T 1) = _
  rw [PolygonUniversalScaling.overlapScale_T_one]
  simp [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]

end FLT.Mazur.PolygonInfinitesimal
