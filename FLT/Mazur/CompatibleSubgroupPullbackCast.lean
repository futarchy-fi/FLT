/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupBaseChangeCoherence

/-!
# Projection formulas for subgroup comparisons constructed by rewriting

Rewriting an equality of parameter maps agrees with the full compatible
pullback comparison. Both directions retain the original whole-curve projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (g : T ⟶ S) (k : U ⟶ T)
  (f : U ⟶ S) (w : f = k ≫ g)

/-- A rewritten compatible presentation is its actual equal-composite pullback transport. -/
theorem compatibleBaseChangeCompEq_cast {D : GeneralizedEllipticCurve U}
    {J : D.FiniteSubgroup n} (a : CompatibleIso J (H.baseChange f)) :
    (by
      have b := a
      rw [w] at b
      exact b.trans (compatibleBaseChangeComp H g k)) =
      a.trans (compatibleBaseChangeCompEq H g k f w) := by
  subst f
  rfl

/-- The direct-to-iterated compatible comparison preserves the original curve projection. -/
@[reassoc] theorem compatibleBaseChangeCompEq_curve_fst :
    (compatibleBaseChangeCompEq H g k f w).curve.hom.curve.left ≫
      pullback.fst (E.baseChange g).curve.hom k ≫ pullback.fst E.curve.hom g =
        pullback.fst E.curve.hom f := by
  rw [compatibleBaseChangeCompEq_curve]
  exact E.baseChangeCompEqIso_curve_fst g k f w

/-- The inverse compatible comparison also retains the full original curve projection. -/
@[reassoc] theorem compatibleBaseChangeComp_inv_curve_fst :
    (compatibleBaseChangeComp H g k).curve.inv.curve.left ≫
        pullback.fst E.curve.hom (k ≫ g) =
      pullback.fst (E.baseChange g).curve.hom k ≫ pullback.fst E.curve.hom g := by
  have hp := congrArg
    ((compatibleBaseChangeComp H g k).curve.inv.curve.left ≫ ·)
    (E.baseChangeCompIso_fst_fst g k)
  have hi : (compatibleBaseChangeComp H g k).curve.inv.curve.left ≫
      (compatibleBaseChangeComp H g k).curve.hom.curve.left = 𝟙 _ :=
    congrArg (fun a ↦ a.curve.left) (compatibleBaseChangeComp H g k).curve.inv_hom_id
  change _ ≫ (compatibleBaseChangeComp H g k).curve.hom.curve.left ≫ _ = _ at hp
  rw [← Category.assoc, hi, Category.id_comp] at hp
  exact hp.symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
