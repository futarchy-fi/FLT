/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonOneGonContraction

/-!
# The specified contraction maps in original one-gon coordinates

The retained component is exactly the original normalization, and the target
node is the origin of the original nodal chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonOneGonContraction
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The retained component uses the full original normalization parameterization. -/
theorem retainedComponent_left :
    (retainedComponent K).left = OneGonNormalization.normalization K := by
  change (PolygonPinching.componentι K 1 0 ≫ OneGonNormalization.normalizationOver K).left = _
  rw [OneGonNormalization.componentι_normalizationOver]
  rfl

/-- The target node is the full original origin section. -/
theorem targetNode_left :
    (targetNode K).left = PolygonNodePresentation.bOrigin K ≫ OneGonGluing.node K := by
  exact OneGonNormalization.nodeι_nodes K 0

/-- The collapse to the coefficient point retains its original structure map. -/
theorem componentToPoint_left :
    (componentToPoint K).left = ProjectiveLine.toBase K := rfl

end FLT.Mazur.PolygonOneGonContraction
