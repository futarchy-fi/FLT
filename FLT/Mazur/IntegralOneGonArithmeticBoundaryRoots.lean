/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonOriginalBaseChange
public import FLT.Mazur.IntegralOneGonBoundaryLevels

/-!
# Integral boundary roots retain their arithmetic source

The actual field pullback of the roots over Z agrees with the original root
subgroup on the specified boundary fiber of the degeneration over Z[[t]].
This comparison is on the field fiber; it does not extend a subgroup off it.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.IntegralOneGonArithmeticBoundaryRoots

open OneGonSmoothing CharacterSchemeBaseChange GeneralizedEllipticCurve.FiniteSubgroup

variable (K : Type) [Field K] (n : ℕ) [NeZero n]

/-- The actual arithmetic root pullback agrees with the root on the integral boundary fiber. -/
def compatibleIso : CompatibleIso
    ((ArithmeticOneGonRoots.subgroup ℤ n).baseChange (baseMap ℤ K))
    (IntegralOneGonBoundaryLevels.subgroup K (originalRootsOfUnitySubgroup K n)) :=
  (ArithmeticOneGonOriginalBaseChange.compatibleIso ℤ K n).symm.trans
    (IntegralOneGonBoundaryLevels.compatibleIso K (originalRootsOfUnitySubgroup K n))

/-- The whole-curve comparison goes through the same original pinched curve. -/
theorem compatibleIso_curve :
    (compatibleIso K n).curve = (ArithmeticOneGonOriginalBaseChange.curveIso ℤ K).symm ≪≫
      IntegralOneGonBoundaryLevels.curveIso K := by
  change ((_ ≪≫ Iso.refl _).symm ≪≫ _) = _
  rw [Iso.trans_refl]
  rfl

/-- The subgroup map is the inverse of the original arithmetic root comparison. -/
theorem compatibleIso_subgroup :
    (compatibleIso K n).subgroup.hom =
      (RootsOfUnityArithmeticPullback.comparison ℤ K n).inv := by
  change (_ ≫ 𝟙 _) ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.comp_id]
  rfl

/-- The entire integral-fiber ideal is the transported actual arithmetic root ideal. -/
theorem subgroup_ideal :
    (IntegralOneGonBoundaryLevels.subgroup K (originalRootsOfUnitySubgroup K n)).ideal =
      ((ArithmeticOneGonRoots.subgroup ℤ n).baseChange (baseMap ℤ K)).ideal.comap
        (compatibleIso K n).curve.inv.curve.left :=
  ideal_transport _ _ (compatibleIso K n).curve (compatibleIso K n).subgroup
    (compatibleIso K n).compatible

/-- The specified integral boundary level is the actual pullback of the arithmetic root class. -/
theorem level_class :
    (Quotient.mk _ (IntegralOneGonBoundaryLevels.level K (originalRootsOfUnitySubgroup K n)
      (originalRootsOfUnitySubgroup_isCyclic K n) (originalRootsOfUnitySubgroup_isAmple K n)) :
        ampleCyclicClasses (Spec (.of K)) n) =
      ampleCyclicClassesPullback (baseMap ℤ K) n
        (Quotient.mk _ (ArithmeticOneGonOriginalRoots.level n ℤ)) :=
  Quotient.sound ⟨(compatibleIso K n).symm⟩

end FLT.Mazur.IntegralOneGonArithmeticBoundaryRoots
