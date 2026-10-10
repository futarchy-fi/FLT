/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBoundary
public import FLT.Mazur.WeierstrassSuccessiveXFlat
public import FLT.Mazur.WeierstrassModificationFlat

/-!
# Structure morphisms of the actual finite-depth charts

The original cubic map on each divided chart is its algebra structure map.
The successive x-direction contraction preserves these structure maps, and
its composite is flat over a Bezout domain with nonzero parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (d : Data W π k)
open WeierstrassIntegralChart

/-- The divided contraction retains exactly its original algebra structure. -/
@[reassoc] theorem toCurve_structure :
    toCurve d ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6))) :=
  WeierstrassDilatation.toCurve_structure _ _ _ _ _ _ _ _

/-- Every actual divided chart is flat over its coefficient ring. -/
instance chart_structure_flat : Flat (toCurve d ≫ integralCurveStructure W) := by
  rw [toCurve_structure]
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- Parameter normalization preserves the actual coefficient structure map. -/
@[reassoc] theorem dividedParameter_structure (s t b3 b4 b6 c3 c4 c6 : R)
    (hs : s = t) (h3 : b3 = c3) (h4 : b4 = c4) (h6 : b6 = c6) :
    (WeierstrassDilatation.parameterSpecIso W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (WeierstrassDilatation.Coordinate W s b3 b4 b6))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (WeierstrassDilatation.Coordinate W t c3 c4 c6))) := by
  subst t c3 c4 c6
  simp [WeierstrassDilatation.parameterSpecIso, WeierstrassDilatation.parameterEquiv]

variable [IsDomain R] (hπ : π ≠ 0) (e : Data W π (k + 1))

/-- A normalized successive x contraction preserves the base algebra map. -/
@[reassoc] theorem xContraction_structure :
    xContraction hπ d e ≫ toCurve d ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (WeierstrassSuccessiveX.Coordinate W (π ^ k) π e.b3 e.b4 e.b6))) := by
  rw [toCurve_structure, xContraction, Category.assoc, dividedParameter_structure]
  rw [WeierstrassSuccessiveX.toDivided, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (WeierstrassSuccessiveX.fromDivided W (π ^ k) π e.b3 e.b4 e.b6).comp_algebraMap

/-- Each actual successive x chart is flat over the original Bezout domain. -/
theorem stepX_structure_flat [IsBezout R] :
    Flat (xContraction hπ d e ≫ toCurve d ≫ integralCurveStructure W) := by
  rw [xContraction_structure]
  let _ := WeierstrassSuccessiveX.coordinate_flat_of_parameter_ne_zero
    W (π ^ k) π e.b3 e.b4 e.b6 hπ
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

end FLT.Mazur.WeierstrassDividedDepth
