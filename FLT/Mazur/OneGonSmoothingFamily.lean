/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import FLT.Mazur.WeierstrassIntegralProper
public import FLT.Mazur.WeierstrassIntegralBaseChange
public import FLT.Mazur.WeierstrassIntegralSmooth

/-!
# The pointed proper flat cubic for the one-gon smoothing

Instantiate the existing integral Weierstrass construction with the explicit
one-parameter equation. The resulting family includes the singular closed
fiber; its field fibers with nonzero parameter are smooth.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (t : R)

/-- The actual glued projective cubic over its original coefficient ring. -/
def family : Over (Spec (.of R)) := Over.mk (integralCurveStructure (equation t))

/-- The constructed cubic family is proper, including along its singular fiber. -/
theorem family_proper : IsProper (family t).hom :=
  integralCurveStructure_proper (equation t)

/-- The actual cubic family is flat over the entire coefficient base. -/
theorem family_flat : Flat (family t).hom := integralCurveStructure_flat (equation t)

/-- The constructed cubic has finite presentation locally on its source and target. -/
theorem family_lfp : LocallyOfFinitePresentation (family t).hom :=
  integralCurveStructure_finitePresentation (equation t)

/-- The original infinity point is the marking on the smoothing family. -/
def marking : Spec (.of R) ⟶ (family t).left := integralCurveZero (equation t)

/-- The retained infinity marking is an actual section of the constructed structure map. -/
@[reassoc]
theorem marking_toBase : marking t ≫ (family t).hom = 𝟙 _ :=
  integralCurveZero_structure (equation t)

/-- The actual field-valued family is smooth of dimension one away from parameter zero. -/
theorem fieldFamily_smooth_dimension (K L : Type u) [Field K] [Field L]
    (f : PowerSeries K →+* L) (ht : f PowerSeries.X ≠ 0) :
    SmoothOfRelativeDimension 1 (family (f PowerSeries.X)).hom := by
  have he := fieldFiber_isElliptic K f ht
  rw [equation_map] at he
  exact integralCurveStructure_smooth_dimension _ he.isUnit

end FLT.Mazur.OneGonSmoothing
