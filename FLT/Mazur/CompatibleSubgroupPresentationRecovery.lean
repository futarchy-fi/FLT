/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupPresentationExtension

/-!
# Recovering comparisons from extended subgroup presentations

Transport back through an extended presentation recovers the supplied subgroup
comparison. This permits independently constructed pullback maps to enter the
presentation cocycle without replacing their full compatible data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (p : T ⟶ S)
  {D : GeneralizedEllipticCurve T} {A : D.FiniteSubgroup n}
  (a : CompatibleIso A (H.baseChange p)) (q : U ⟶ T)
  {F : GeneralizedEllipticCurve U} {B : F.FiniteSubgroup n}
  (b : CompatibleIso B (A.baseChange q))

/-- The comparison used to extend a presentation is its exact refinement transport. -/
theorem compatibleRefinementTransport_extension_recovery :
    compatibleRefinementTransport H p (q ≫ p) q rfl a
      (compatiblePresentationExtension H p a q b) = b := by
  simp only [compatibleRefinementTransport, compatiblePresentationExtension,
    compatibleBaseChangeCompEq, CompatibleIso.trans_assoc,
    CompatibleIso.symm_trans_assoc, CompatibleIso.trans_symm, CompatibleIso.trans_refl]

/-- The extended presentation commutes with the original comparison after pullback. -/
theorem compatiblePresentationExtension_presentation :
    (compatiblePresentationExtension H p a q b).trans
      (compatibleBaseChangeComp H p q) = b.trans (a.baseChange q) := by
  simp only [compatiblePresentationExtension, CompatibleIso.trans_assoc,
    CompatibleIso.symm_trans, CompatibleIso.trans_refl]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
