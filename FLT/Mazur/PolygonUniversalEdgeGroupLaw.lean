/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonUniversalEdgeAlgebra
public import FLT.Mazur.ProjectiveLineActionTorus

/-!
# The original universal edge scaling is actual multiplicative-group multiplication

The two unchanged Laurent projections determine a point of the group product.
Its multiplication is the existing universal edge map, as a scheme morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimal
open ProjectiveLineActionPoints
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]
local notation "A" => K[T;T⁻¹][T;T⁻¹]
local notation "U" => MultiplicativeGroupScheme.gm K

/-- The full double Laurent coordinate map multiplies by the actual torus group law. -/
theorem universalEdgePair_mul (f : Spec (.of (A)) ⟶ ((U) ⊗ (U)).left)
    (hf : f ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : K[T;T⁻¹] →+* A)))
    (hs : f ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
      (PolygonScalingNaturality.coeffMap (LaurentPolynomial.C : K →+* K[T;T⁻¹])))) :
    f ≫ (μ[U]).left = universalEdgeScaling K := by
  let a : (A)ˣ := Units.map (LaurentPolynomial.C : K[T;T⁻¹] →+* A).toMonoidHom
    (PolygonUniversalScaling.u (R := K))
  let c : (A)ˣ := PolygonUniversalScaling.u
  have ha : groupPoint K (A) a =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : K[T;T⁻¹] →+* A)) := by
    unfold groupPoint
    congr 1
    apply CommRingCat.hom_ext
    apply PolygonScalingNaturality.ringHom_ext <;>
      simp [a, LaurentUnitPoints.evalUnit, PolygonUniversalScaling.u,
        PolygonChartScaling.coordinateUnit]
  have hc : groupPoint K (A) c = Spec.map (CommRingCat.ofHom
      (PolygonScalingNaturality.coeffMap (LaurentPolynomial.C : K →+* K[T;T⁻¹]))) := by
    rfl
  rw [groupPoint_mul K (A) a c f (hf.trans ha.symm) (hs.trans hc.symm)]
  have hu : LaurentUnitPoints.pointUnit (universalEdgeAlgebra K) = a * c :=
    universalEdgeAlgebra_coordinate K
  rw [← hu, groupPoint_pointUnit, universalEdgeScaling_spec]

end FLT.Mazur.PolygonInfinitesimal
