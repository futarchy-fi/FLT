/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupParameterRefinement
public import FLT.Mazur.GeneralizedCurveIteratedProjection

/-!
# Original coordinates of compatible parameter refinements

Refining a normalized family and its comparison parameter preserves the
projection to the original curve, through all three pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S A B Q R : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (q : A ⟶ S) (q' : B ⟶ S) (k : B ⟶ A)
  (hq : q' = k ≫ q) (s : R ⟶ A) (m : Q ⟶ R) (t : Q ⟶ B) (v : Q ⟶ A)
  (hp : v = m ≫ s) (ht : v = t ≫ k)
local notation "a" => compatibleBaseChangeCompEq H q k q' hq
local notation "r" => compatibleParameterRefinement s m k t v hp ht a

/-- The full compatible refinement preserves the original curve coordinate. -/
@[reassoc] theorem compatibleParameterRefinement_original_curve_fst :
    (r).curve.hom.curve.left ≫ pullback.fst _ m ≫ pullback.fst _ s ≫
      pullback.fst E.curve.hom q = pullback.fst _ t ≫ pullback.fst E.curve.hom q' := by
  rw [compatibleParameterRefinement_curve, compatibleBaseChangeCompEq_curve]
  change ((baseChangeMap t (E.baseChangeCompEqIso q k q' hq).hom).curve.left ≫
    ((E.baseChange q).baseChangeCompEqIso k t v ht).inv.curve.left ≫
      ((E.baseChange q).baseChangeCompEqIso s m v hp).hom.curve.left) ≫ _ = _
  simp only [Category.assoc, baseChangeCompEqIso_curve_fst_assoc,
    baseChangeCompEqIso_inv_curve_fst_assoc, baseChangeMap_fst_assoc,
    baseChangeCompEqIso_curve_fst]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
