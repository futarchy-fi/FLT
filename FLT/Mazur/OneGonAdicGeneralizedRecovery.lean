/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientIso
public import FLT.Mazur.OneGonAdicSmoothGroupRecovery
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Full generalized-curve recovery of the finite smooth-stage model

The original complete arithmetic one-gon is the actual pullback of the enlarged
finite coefficient model as a generalized elliptic curve. Its whole-curve
projection agrees with the previously constructed Cartesian recovery map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing CharacterSchemeBaseChange GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- Recover the finite smooth-stage model with its entire arithmetic group action. -/
irreducible_def smoothModelGeneralizedRecoveryIso :
    ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht) ≅
      (smoothModelCurve I t ht n).baseChange (baseMap (smoothModelBase I t ht n) R) :=
  ArithmeticOneGonGeneralizedCurve.coefficientIso (S := R)
    (algebraicParameter I t ht n) (algebraicParameter_complementaryUnit I t ht n) ≪≫
      (algebraicCurve I t ht n).baseChangeCompEqIso (smoothModelBaseMap I t ht n)
        (baseMap (smoothModelBase I t ht n) R) (baseMap (algebraicBase I t ht n) R)
        (smoothModelBaseMap_comp I t ht n).symm

/-- Full DR recovery retains the initial whole-cubic coefficient projection. -/
@[reassoc] theorem smoothModelGeneralizedRecoveryIso_fst_fst :
    (smoothModelGeneralizedRecoveryIso I t ht n).hom.curve.left ≫
      pullback.fst (smoothModelCurve I t ht n).curve.hom
        (baseMap (smoothModelBase I t ht n) R) ≫
          pullback.fst (algebraicCurve I t ht n).curve.hom (smoothModelBaseMap I t ht n) =
            algebraicProjection I t ht n := by
  rw [smoothModelGeneralizedRecoveryIso_def]
  change (_ ≫ _) ≫ _ ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (ArithmeticOneGonGeneralizedCurve.coefficientIso (S := R)
      (algebraicParameter I t ht n) (algebraicParameter_complementaryUnit I t ht n)).hom.curve.left
        ≫ f) (baseChangeCompEqIso_curve_fst (algebraicCurve I t ht n)
          (smoothModelBaseMap I t ht n) (baseMap (smoothModelBase I t ht n) R)
          (baseMap (algebraicBase I t ht n) R) (smoothModelBaseMap_comp I t ht n).symm)).trans
      (ArithmeticOneGonGeneralizedCurve.coefficientIso_curve_fst _ _))

/-- The full comparison recovers exactly the existing enlarged whole-curve map. -/
@[reassoc] theorem smoothModelGeneralizedRecoveryIso_fst :
    (smoothModelGeneralizedRecoveryIso I t ht n).hom.curve.left ≫
      pullback.fst (smoothModelCurve I t ht n).curve.hom
        (baseMap (smoothModelBase I t ht n) R) = smoothModelCurveRecovery I t ht n := by
  apply pullback.hom_ext
  · rw [Category.assoc, smoothModelCurveRecovery_fst]
    exact smoothModelGeneralizedRecoveryIso_fst_fst I t ht n
  · change (_ ≫ _) ≫ (smoothModelCurve I t ht n).curve.hom =
      smoothModelCurveRecovery I t ht n ≫ (smoothModelCurve I t ht n).curve.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hw := (smoothModelGeneralizedRecoveryIso I t ht n).hom.curve.w
    change _ ≫ pullback.snd _ _ = _ at hw
    rw [hw, (smoothModelCurveRecovery_isPullback I t ht n).w]
    rfl

end FLT.Mazur.OneGonAdicCharacterTower
