/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeChart
public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeNodeChart
public import FLT.Mazur.WeierstrassSuccessiveTensorSlopeCoordinates

/-!
# Both constructed arithmetic branches in the original tensor coordinates

A Boolean selects the already constructed small or opposite branch. Its
slope solves the original equation, and its tensor evaluation recovers the
existing arithmetic comparison exactly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (π : R) (m : ℕ)

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

local notation "v" => nilpotentNodeSlope (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)
local notation "v'" => oppositeNodeSlope (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)

/-- Select one of the two already constructed original arithmetic slopes. -/
def arithmeticBranchSlope (opposite : Bool) : SuccessiveIncidence.Coordinate (q π) :=
  if opposite then v' else v

/-- Either selected slope satisfies the same original arithmetic equation. -/
theorem arithmeticBranchSlope_equation (opposite : Bool) :
    arithmeticBranchSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite ^ 2 +
      nodeSlopeLinear (W.map q) (q π) (q b3) *
        arithmeticBranchSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite =
      nodeSlopeConstant (W.map q) (q s) (q π) (q b4) (q b6) := by
  cases opposite
  · exact nilpotentNodeSlope_equation (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
      (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
      (arithmeticCoefficient_mem π m h6)
  · exact oppositeNodeSlope_equation (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
      (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
      (arithmeticCoefficient_mem π m h6)

/-- Either existing arithmetic node chart with its original tensor algebra as target. -/
def arithmeticTensorBranchChart (opposite : Bool) :
    Spec (.of (PolygonSmoothing.ChartRing (parameter R π m))) ⟶
      Spec (.of (ScalarExtension W s π b3 b4 b6 Q)) :=
  (if opposite then arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6
    else arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6) ≫
      Spec.map (CommRingCat.ofHom (baseChangeEquiv W s π b3 b4 b6 Q).toRingHom)

/-- The selected tensor evaluation is exactly the original constructed arithmetic chart. -/
theorem arithmeticTensorBranchChart_eq (opposite : Bool) :
    Spec.map (CommRingCat.ofHom (tensorSlopePolygonRetraction W s π b3 b4 b6 Q
      (arithmeticBranchSlope π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)
      (arithmeticBranchSlope_equation π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite)).toRingHom) =
        arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite := by
  rw [tensorSlopePolygonRetraction_spec]
  cases opposite
  · have he := nilpotentNodeRetraction_monic (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
      (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
      (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
      (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
      (arithmeticCoefficient_mem π m h6)
    change (Spec.map _ ≫ Spec.map (CommRingCat.ofHom
      (simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) v _).toRingHom)) ≫
        Spec.map _ = _
    rw [show simpleSlopeRetraction (W.map q) (q s) (q π) (q b3) (q b4) (q b6) v _ = _ from he]
    rfl
  · rfl

/-- Both actual arithmetic tensor branches are open immersions. -/
theorem arithmeticTensorBranchChart_isOpenImmersion (opposite : Bool) :
    IsOpenImmersion
      (arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite) := by
  have he : IsIso (CommRingCat.ofHom (baseChangeEquiv W s π b3 b4 b6 Q).toRingHom) :=
    (baseChangeEquiv W s π b3 b4 b6 Q).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold arithmeticTensorBranchChart
  cases opposite <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · have hc := arithmeticNodeChart_isOpenImmersion π m W s b3 b4 b6 ha hs h2 h3 h4 h6
    exact IsOpenImmersion.comp _ _
  · have hc := arithmeticOppositeNodeChart_isOpenImmersion π m W s b3 b4 b6 ha hs h2 h3 h4 h6
    exact IsOpenImmersion.comp _ _

end FLT.Mazur.WeierstrassSuccessiveX
