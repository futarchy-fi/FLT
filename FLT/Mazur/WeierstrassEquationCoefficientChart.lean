/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassProperCoefficientComposition
public import FLT.Mazur.WeierstrassEquationTransport

/-!
# Affine charts of named proper coefficient comparisons

The coefficient chart map retains equation transport and every coordinate
generator. Its spectrum square is the actual proper coefficient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S]
  (W : WeierstrassCurve R) (V : WeierstrassCurve S) (f : R →+* S) (h : V = W.map f)

/-- The actual coefficient chart homomorphism for a specified equation equality. -/
def properCoefficientChartMap (j : Fin 3) : Coordinate W j →+* Coordinate V j := by
  let _ : Algebra R S := f.toAlgebra
  exact (chartEquationMap h.symm j).toRingHom.comp
    (chartCoefficientMap (S := S) W j).toRingHom

/-- Named coefficient chart maps retain each original coordinate generator. -/
theorem properCoefficientChartMap_coord (j i : Fin 3) :
    properCoefficientChartMap W V f h j (coord W j i) = coord V j i := by
  let _ : Algebra R S := f.toAlgebra
  change chartEquationMap h.symm j (chartCoefficientMap (S := S) W j (coord W j i)) = _
  rw [chartCoefficientMap_coord]
  exact chartEquationMap_coord h.symm j i

/-- Coefficients are mapped by the specified ring homomorphism. -/
theorem properCoefficientChartMap_coeff (j : Fin 3) (r : R) :
    properCoefficientChartMap W V f h j (algebraMap R (Coordinate W j) r) =
      algebraMap S (Coordinate V j) (f r) := by
  subst V
  let _ : Algebra R S := f.toAlgebra
  exact (chartCoefficientMap (S := S) W j).commutes r

/-- The affine coefficient map is the restriction of the actual proper coefficient morphism. -/
@[reassoc] theorem properCoefficientChartMap_chart (j : Fin 3) :
    Spec.map (CommRingCat.ofHom (properCoefficientChartMap W V f h j)) ≫
        integralCurveChart W j = integralCurveChart V j ≫ properCoefficientMap W V f h := by
  subst V
  let _ : Algebra R S := f.toAlgebra
  change Spec.map (CommRingCat.ofHom (chartCoefficientMap (S := S) W j).toRingHom) ≫
    integralCurveChart W j = integralCurveChart (W.map f) j ≫
      (𝟙 _ ≫ integralCoefficientMorphism W)
  rw [Category.id_comp]
  exact (integralCurveChart_coefficientMorphism (S := S) W j).symm

end FLT.Mazur.WeierstrassIntegralChart
