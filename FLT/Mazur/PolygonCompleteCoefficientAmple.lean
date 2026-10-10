/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientAmple
public import FLT.Mazur.PolygonCompleteBoundaryCoordinateTransport
public import FLT.Mazur.ProperAmpleConverse

/-!
# Ampleness on the actual complete polygon candidate

The original homogeneous coefficient sections give affine generator opens.
Thus the constructed coefficient line is ample and relatively ample over the
original complete base, including in the projective-presentation sense.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] completeCoefficientCoordinates

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Each original complete coordinate generates exactly on its original chart. -/
theorem completeCoefficientSection_generatorOpen
    (i : (completeCoefficientCoordinates K n h).Index) :
    sectionGeneratorOpen (completeCoefficientLine K n h) (completeCoefficientSection K n h i) =
      GradedProjLine.chart (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))
        (completeCoefficientCoordinates K n h).coordinate i :=
  GradedProjLine.coefficientSection_generatorOpen _ _ _
    (completeCoefficientCoordinates K n h).positive (completeCoefficientCoordinates K n h).covers i

/-- The original complete coefficient line is relatively ample in the section sense. -/
theorem completeCoefficientLine_relativelyAmple :
    RelativelyAmpleLineBundle (exactVeroneseProjToBase K n h) (completeCoefficientLine K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact GradedProjLine.coefficientLine_relativelyAmple _ _ _ (exactVeroneseProjToBase K n h)
    (completeCoefficientCoordinates K n h).positive (completeCoefficientCoordinates K n h).covers

/-- The same complete coefficient line is ample on the actual proper candidate. -/
theorem completeCoefficientLine_ample : AmpleLineBundle (completeCoefficientLine K n h) :=
  (completeCoefficientLine_relativelyAmple K n h).ample_of_affine

/-- A positive power of the original complete coefficient line has a projective presentation. -/
theorem completeCoefficientLine_relativeAmple :
    RelativeAmple (exactVeroneseProjToBase K n h)
      (completeCoefficientLine K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact (completeCoefficientLine_relativelyAmple K n h).relativeAmple

end FLT.Mazur.PolygonInfinitesimalStages
