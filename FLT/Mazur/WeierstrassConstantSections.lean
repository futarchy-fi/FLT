/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperIntegralConstantSections
public import FLT.Mazur.WeierstrassGeometricIntegral
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Constant functions on the actual Weierstrass cubic and its fibers

The actual zero section and proper integrality prove that every global function
is constant. The same result holds on any field-valued Cartesian square,
including singular fibers, and computes the actual zeroth structure cohomology.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.FCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {K : Type} [Field K] (W : WeierstrassCurve K)

/-- The actual cubic over any field has only constant global functions. -/
theorem integralCurve_constantGlobalSections :
    HasConstantGlobalSections (integralCurveStructure W) :=
  constantGlobalSections_of_proper_integral_section _ (integralCurveZero W)
    (integralCurveZero_structure W)

/-- The original base field is canonically the cubic's actual zeroth cohomology. -/
def integralCurveH0Equiv : K ≃ₗ[K] H0 (integralCurveStructure W) :=
  scalarH0ConstantsEquiv _ (integralCurve_constantGlobalSections W)

/-- The degree-zero structure cohomology has dimension one even for singular cubics. -/
theorem integralCurveH0_finrank : Module.finrank K (H0 (integralCurveStructure W)) = 1 :=
  finrank_H0_of_constantGlobalSections _ (integralCurve_constantGlobalSections W)

variable {R : Type} [CommRing R] (E : WeierstrassCurve R)
  (s : Spec (.of K) ⟶ Spec (.of R)) {Y : Scheme}
  (fst : Y ⟶ integralCurve E) (snd : Y ⟶ Spec (.of K))
  (h : IsPullback fst snd (integralCurveStructure E) s)

/-- The zero section supplies a rational point on every field-valued fiber square. -/
def integralCurveFieldSquareZero : Spec (.of K) ⟶ Y :=
  h.lift (s ≫ integralCurveZero E) (𝟙 _)
    (by rw [Category.assoc, integralCurveZero_structure, Category.comp_id, Category.id_comp])

/-- The constructed field-fiber point is a section of the specified fiber structure map. -/
@[reassoc] theorem integralCurveFieldSquareZero_section :
    integralCurveFieldSquareZero E s fst snd h ≫ snd = 𝟙 _ :=
  h.lift_snd _ _ _

include h in
/-- Constant functions on every field-valued fiber, with its original structure map. -/
theorem integralCurveFieldSquare_constantGlobalSections : HasConstantGlobalSections snd := by
  let _ := integralCurveFieldSquare_isIntegral E s fst snd h
  let _ : IsProper snd := MorphismProperty.of_isPullback h inferInstance
  exact constantGlobalSections_of_proper_integral_section snd
    (integralCurveFieldSquareZero E s fst snd h)
    (integralCurveFieldSquareZero_section E s fst snd h)

include h in
/-- Every field-valued fiber has one-dimensional actual degree-zero cohomology. -/
theorem integralCurveFieldSquareH0_finrank : Module.finrank K (H0 snd) = 1 :=
  finrank_H0_of_constantGlobalSections snd
    (integralCurveFieldSquare_constantGlobalSections E s fst snd h)

end FLT.Mazur.WeierstrassIntegralChart
