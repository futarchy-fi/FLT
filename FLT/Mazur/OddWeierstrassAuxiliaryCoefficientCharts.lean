/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassEquationCoefficientChart
public import FLT.Mazur.OddWeierstrassAuxiliaryCoefficientNaturality

/-!
# The actual odd coefficient comparisons on affine charts

Both comparisons retain their specified equation transports. Original coordinate
evaluation recovers the entire original affine section algebra.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open WeierstrassIntegralChart
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (OddChartRing oddChartEquation)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original coefficient chart map retains the original equation transport. -/
def auxiliaryOriginalChartMap (j : Fin 3) :
    Coordinate oddChartEquation j →+* Coordinate (auxiliaryPullbackEquation g) j :=
  properCoefficientChartMap oddChartEquation _ (auxiliaryCoefficientHom g)
    (auxiliaryPullbackEquation_coefficient g) j

/-- The normalized coefficient chart map retains the normalized equation transport. -/
def auxiliaryNormalizedChartMap (j : Fin 3) :
    Coordinate oddChartEquation j →+* Coordinate (auxiliaryNormalizedEquation g) j :=
  properCoefficientChartMap oddChartEquation _ (auxiliaryNormalizedCoefficientHom g)
    (auxiliaryNormalizedCoefficientHom_equation g).symm j

/-- Original coordinate generators remain the actual generators after coefficient change. -/
theorem auxiliaryOriginalChartMap_coord (j i : Fin 3) :
    auxiliaryOriginalChartMap g j (coord oddChartEquation j i) =
      coord (auxiliaryPullbackEquation g) j i := properCoefficientChartMap_coord ..

/-- Normalized coordinate generators remain the actual generators after coefficient change. -/
theorem auxiliaryNormalizedChartMap_coord (j i : Fin 3) :
    auxiliaryNormalizedChartMap g j (coord oddChartEquation j i) =
      coord (auxiliaryNormalizedEquation g) j i := properCoefficientChartMap_coord ..

/-- The original affine chart square retains the actual proper coefficient projection. -/
@[reassoc] theorem auxiliaryOriginalChartMap_chart (j : Fin 3) :
    Spec.map (CommRingCat.ofHom (auxiliaryOriginalChartMap g j)) ≫
        integralCurveChart oddChartEquation j =
      integralCurveChart (auxiliaryPullbackEquation g) j ≫
        auxiliaryOriginalCoefficientProjection g := properCoefficientChartMap_chart ..

/-- The normalized affine chart square retains the actual proper coefficient projection. -/
@[reassoc] theorem auxiliaryNormalizedChartMap_chart (j : Fin 3) :
    Spec.map (CommRingCat.ofHom (auxiliaryNormalizedChartMap g j)) ≫
        integralCurveChart oddChartEquation j =
      integralCurveChart (auxiliaryNormalizedEquation g) j ≫
        auxiliaryNormalizedCoefficientProjection g := properCoefficientChartMap_chart ..

/-- Original affine coordinate evaluation recovers the full original coordinate algebra map. -/
theorem auxiliaryPullbackEvaluation_coefficient (a : Labels 3) (ha : a ≠ 1) :
    (auxiliaryPullbackEvaluation g a ha).toRingHom.comp (auxiliaryOriginalChartMap g 2) =
      g.comp (auxiliaryCoordinateSections a ha) := by
  let _ : Algebra OddChartRing R := (auxiliaryCoefficientHom g).toAlgebra
  let u : Coordinate oddChartEquation 2 →ₐ[OddChartRing] R :=
    { toRingHom := (auxiliaryPullbackEvaluation g a ha).toRingHom.comp
        (auxiliaryOriginalChartMap g 2)
      commutes' := fun r => by
        change auxiliaryPullbackEvaluation g a ha
          (auxiliaryOriginalChartMap g 2 (algebraMap _ _ r)) = _
        rw [auxiliaryOriginalChartMap, properCoefficientChartMap_coeff]
        exact (auxiliaryPullbackEvaluation g a ha).commutes _ }
  let v : Coordinate oddChartEquation 2 →ₐ[OddChartRing] R :=
    { toRingHom := g.comp (auxiliaryCoordinateSections a ha)
      commutes' := fun r => congrArg g (auxiliaryCoordinateSections_coeff a ha r) }
  change u.toRingHom = v.toRingHom
  apply congrArg AlgHom.toRingHom
  apply hom_ext
  intro i
  exact (congrArg (auxiliaryPullbackEvaluation g a ha)
    (auxiliaryOriginalChartMap_coord g 2 i)).trans (auxiliaryPullbackEvaluation_coord g a ha i)

end FLT.Mazur.OddWeierstrassParameter
