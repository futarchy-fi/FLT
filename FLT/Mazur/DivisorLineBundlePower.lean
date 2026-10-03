/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleSumUnit
public import FLT.Mazur.ModuleLineBundleTensorPullback

/-!
# Tensor powers of Cartier divisor line bundles

The actual sheaf O(nD) is the n-fold tensor power of O(D). The zero case
uses the empty-divisor comparison and the successor uses the divisor-sum
comparison. No positivity or projective presentation is assumed.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- Tensor powers of the positive divisor sheaf identify with powers of its ideal. -/
def divisorLineBundlePowerIso (hI : EffectiveCartier I) :
    ∀ n : ℕ, tensorPower (divisorLineBundle I hI) n ≅
      divisorLineBundle (I ^ n) (hI.pow n)
  | 0 => (divisorLineBundleTopIso effectiveCartier_top).symm ≪≫
      divisorLineBundleEqIso (show (⊤ : X.IdealSheafData) = I ^ 0 by simp) _ _
  | n + 1 => ModuleSheafTensor.congr (Iso.refl _) (divisorLineBundlePowerIso hI n) ≪≫
      divisorLineBundleSumIso hI (hI.pow n) ≪≫
      divisorLineBundleEqIso (pow_succ' I n).symm _ _

/-- Degree zero is the empty-divisor comparison with its ideal equality transport. -/
@[simp]
lemma divisorLineBundlePowerIso_zero (hI : EffectiveCartier I) :
    divisorLineBundlePowerIso hI 0 = (divisorLineBundleTopIso effectiveCartier_top).symm ≪≫
      divisorLineBundleEqIso (show (⊤ : X.IdealSheafData) = I ^ 0 by simp) _ _ := rfl

/-- The successor comparison is induced by multiplication of divisor ideals. -/
@[simp]
lemma divisorLineBundlePowerIso_succ (hI : EffectiveCartier I) (n : ℕ) :
    divisorLineBundlePowerIso hI (n + 1) =
      ModuleSheafTensor.congr (Iso.refl _) (divisorLineBundlePowerIso hI n) ≪≫
        divisorLineBundleSumIso hI (hI.pow n) ≪≫
        divisorLineBundleEqIso (pow_succ' I n).symm _ _ := rfl

end FLT.Mazur.FCurve
