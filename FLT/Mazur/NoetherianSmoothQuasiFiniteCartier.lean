/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothQuasiFiniteCartierCriterion
public import FLT.Mazur.FiniteLocallyFreeDegreeAffine
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Flat quasi-finite closed families on smooth curves over Noetherian bases

Every affine ideal is finitely presented on a locally Noetherian smooth
curve. The general presented-ideal criterion therefore applies to arbitrary
ambient curves, without any support-containing affine chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f]

/-- A locally Noetherian ambient supplies all affine ideal presentations. -/
theorem relativeEffectiveCartier_of_noetherian_smooth_quasiFinite_flat
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [LocallyQuasiFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)] :
    RelativeEffectiveCartier f I := by
  apply relativeEffectiveCartier_of_smooth_quasiFinite_flat_presented f I
  intro V
  let _ := IsLocallyNoetherian.component_noetherian V
  exact Module.finitePresentation_of_finite Γ(X, V) (I.ideal V)

/-- Locally Noetherian coefficients suffice for the unrestricted smooth curve criterion. -/
theorem relativeEffectiveCartier_of_smooth_quasiFinite_flat_noetherian_base
    [IsLocallyNoetherian Y] (I : X.IdealSheafData)
    [LocallyQuasiFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)] :
    RelativeEffectiveCartier f I := by
  let _ : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact relativeEffectiveCartier_of_noetherian_smooth_quasiFinite_flat f I

/-- Every finite locally free closed family on such a curve is a relative Cartier divisor. -/
theorem relativeEffectiveCartier_of_smooth_degree_noetherian_base
    [IsLocallyNoetherian Y] (I : X.IdealSheafData) (d : ℕ)
    (h : FiniteLocallyFreeDegree (I.subschemeι ≫ f) d) : RelativeEffectiveCartier f I := by
  let _ := h.1
  let _ := h.2.1
  exact relativeEffectiveCartier_of_smooth_quasiFinite_flat_noetherian_base f I

end FLT.Mazur.FCurve
