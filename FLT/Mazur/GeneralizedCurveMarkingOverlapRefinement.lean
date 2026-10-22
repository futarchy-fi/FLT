/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingOverlap
public import FLT.Mazur.GeneralizedCurveSquareProjection

/-!
# Compatibility of the actual overlap families under refinement

Refining a common chart and recomputing the overlap gives the same full family
map as pulling back the old overlap and using the actual associators on both
sides. Only equality of the original base maps is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V Z : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ S) (p : V ⟶ T) (q : V ⟶ U)
  (p' : Z ⟶ T) (q' : Z ⟶ U) (m : Z ⟶ V)
  (w : q ≫ h = p ≫ g) (w' : q' ≫ h = p' ≫ g)
  (hp : p' = m ≫ p) (hq : q' = m ≫ q)

/-- Recomputed overlap families commute with the actual two restriction associators. -/
theorem smoothMarkingOverlap_refine :
    (baseChangeSquare g h q' p' w').app E ≪≫
      (E.baseChange g).baseChangeCompEqIso p m p' hp =
    (E.baseChange h).baseChangeCompEqIso q m q' hq ≪≫
      (baseChangeFunctor m).mapIso ((baseChangeSquare g h q p w).app E) := by
  apply baseChangeSquareIso_refine E h q' q m g p g p' w' w hq
  exact baseChangeCompEqIso_curve_fst_assoc (E.baseChange g) p m p' hp
    (Limits.pullback.fst E.curve.hom g)

end FLT.Mazur.GeneralizedEllipticCurve
