/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineHomogeneousCoefficient
public import FLT.Mazur.NodeTangentProjectiveLineDescent

/-!
# The tangent coefficient action is the full glued coefficient map

Identify the exterior's homogeneous coefficient operation with the coefficient
map used on the independently constructed exceptional projective components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
  [Fact (Irreducible (nodeTangentPolynomial W))]

/-- The exterior and exceptional components use exactly the same whole coefficient map. -/
theorem nodeTangentLineCoefficients_eq_coefficientMap :
    nodeTangentLineCoefficients W =
      ProjectiveLine.coefficientMap (nodeTangentConjugation W).toAlgHom.toRingHom := by
  rw [nodeTangentLineCoefficients, ProjectiveLine.homogeneousIso_coefficientMap_assoc,
    Iso.hom_inv_id, Category.comp_id]
  rfl

end FLT.Mazur
