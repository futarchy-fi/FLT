/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionMap
public import FLT.Mazur.DivisorCanonicalOperations
/-!
# Canonical sections under composed divisor comparisons

Keep the unit and addition calculations separate from tensor-power induction.
The comparisons include the actual ideal equality transports.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}}
variable {I J L : X.IdealSheafData}
/-- Divisor addition followed by ideal transport preserves canonical sections. -/
lemma divisorSection_sum_eq (hI : EffectiveCartier I) (hJ : EffectiveCartier J)
    (hL : EffectiveCartier L) (he : I * J = L) (U : X.Opens) :
    (divisorLineBundleSumIso hI hJ ≪≫ divisorLineBundleEqIso he (hI.mul hJ) hL).hom.app U
      (ModuleSheafTensor.pure _ _ U (divisorSection hI U) (divisorSection hJ U)) =
      divisorSection hL U :=
  sectionIso_trans_of_eq (divisorLineBundleSumIso hI hJ)
    (divisorLineBundleEqIso he (hI.mul hJ) hL) U _ _ _
    (divisorSection_sum_open hI hJ U) (divisorSection_eqIso he (hI.mul hJ) hL U)
/-- The empty-divisor comparison followed by ideal transport preserves the unit section. -/
lemma divisorSection_top_eq (hJ : EffectiveCartier J)
    (he : (⊤ : X.IdealSheafData) = J) (U : X.Opens) :
    ((divisorLineBundleTopIso effectiveCartier_top).symm ≪≫
      divisorLineBundleEqIso he effectiveCartier_top hJ).hom.app U (1 : Γ(X, U)) =
      divisorSection hJ U :=
  sectionIso_trans_of_eq (divisorLineBundleTopIso effectiveCartier_top).symm
    (divisorLineBundleEqIso he effectiveCartier_top hJ) U _ _ _
    (sectionIso_inv_of_eq (divisorLineBundleTopIso effectiveCartier_top) U _ _
      (divisorSection_top U)) (divisorSection_eqIso he effectiveCartier_top hJ U)
end FLT.Mazur.FCurve
