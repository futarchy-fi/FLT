/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineValuationExtension
public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Complete projective maps detected by their right affine chart

Endpoint reversal transports the proved density of the left chart. Agreement
over the coefficient field then extends from the entire right chart to the whole line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- The complete right affine chart is dominant in the original glued projective line. -/
instance rightChart_isDominant : IsDominant (right K) := by
  have h : right K = left K ≫ (endpointReversalIso K).hom :=
    (left_endpointReversal K).symm
  rw [h]
  infer_instance

/-- Maps to a separated relative target are determined by the entire right affine chart. -/
theorem rightChart_hom_ext {X B : Scheme.{u}} (b : X ⟶ B) [IsSeparated b]
    (f g : scheme K ⟶ X) (hb : f ≫ b = g ≫ b)
    (h : right K ≫ f = right K ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated b hb (right K) h

end FLT.Mazur.ProjectiveLine
