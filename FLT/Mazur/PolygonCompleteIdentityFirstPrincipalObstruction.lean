/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstLaurentCoefficient
public import FLT.Mazur.PolygonCompleteIdentityFirstNodeObstruction

/-!
# Concrete principal parts of the unchanged original action

Extract the parameter coefficient of the actual action-minus-scaling defect
on every reduced node function, then take its canonical principal parts.
The result faithfully represents the original quotient-valued obstruction;
no abstract quotient equality or chosen node extension is needed to compute it.
Its vanishing still requires a geometric argument.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentNodePrincipalParts PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "N" => ChartRing (0 : R)

/-- Canonical Laurent coefficients of the unchanged original action's full reduced defect. -/
def completeIdentityFirstDefectCoefficient : (N) →+ ((R)[T;T⁻¹] × (R)[T;T⁻¹]) :=
  (firstNodePairCoefficient (R)).comp (completeIdentityFirstReducedDefect K n h i)

/-- Weighting these coefficients recovers the complete original defect, including nilpotents. -/
theorem completeIdentityFirstDefectCoefficient_weighted (z : N) :
    firstNodeParameterPair (R) (completeIdentityFirstDefectCoefficient K n h i z) =
      completeIdentityFirstReducedDefect K n h i z :=
  firstNodePairCoefficient_reconstruct (R) _
    (completeIdentityFirstReducedDefect_parameter K n h i z)

/-- The actual reduced-node obstruction in explicit canonical Laurent coordinates. -/
def completeIdentityFirstPrincipalObstruction : (N) →+ ((R)[T;T⁻¹] × (R)[T;T⁻¹]) :=
  principalParts.toAddMonoidHom.comp (completeIdentityFirstDefectCoefficient K n h i)

/-- Every value is already the canonical remainder of its own Laurent pair. -/
theorem completeIdentityFirstPrincipalObstruction_projected (z : N) :
    principalParts (completeIdentityFirstPrincipalObstruction K n h i z) =
      completeIdentityFirstPrincipalObstruction K n h i z :=
  principalParts_idempotent _

/-- Each concrete obstruction has zero constant on its second branch. -/
theorem completeIdentityFirstPrincipalObstruction_right_zero (z : N) :
    (completeIdentityFirstPrincipalObstruction K n h i z).2.coeff 0 = 0 :=
  principalParts_right_zero _

/-- The concrete remainder has exactly the original full node-obstruction class. -/
theorem completeIdentityFirstPrincipalObstruction_class (z : N) :
    firstNodeParameterClass (R) (completeIdentityFirstPrincipalObstruction K n h i z) =
      completeIdentityFirstNodeObstruction K n h i z := by
  change firstNodeParameterClass (R)
    (principalParts (completeIdentityFirstDefectCoefficient K n h i z)) = _
  rw [firstNodeParameterClass_principalParts]
  change QuotientAddGroup.mk' _
    (firstNodeParameterPair (R) (completeIdentityFirstDefectCoefficient K n h i z)) = _
  rw [completeIdentityFirstDefectCoefficient_weighted]
  rfl

/-- Vanishing of the explicit pair is equivalent to vanishing of the original abstract class. -/
theorem completeIdentityFirstPrincipalObstruction_eq_zero_iff (z : N) :
    completeIdentityFirstPrincipalObstruction K n h i z = 0 ↔
      completeIdentityFirstNodeObstruction K n h i z = 0 := by
  rw [← completeIdentityFirstPrincipalObstruction_class,
    firstNodeParameterClass_zero_iff, completeIdentityFirstPrincipalObstruction_projected]

/-- The concrete additive map detects the original obstruction on all node functions. -/
theorem completeIdentityFirstPrincipalObstruction_zero_iff :
    completeIdentityFirstPrincipalObstruction K n h i = 0 ↔
      completeIdentityFirstNodeObstruction K n h i = 0 := by
  constructor
  · intro hz
    apply AddMonoidHom.ext
    intro z
    apply (completeIdentityFirstPrincipalObstruction_eq_zero_iff K n h i z).mp
    rw [hz]
    rfl
  · intro hz
    apply AddMonoidHom.ext
    intro z
    apply (completeIdentityFirstPrincipalObstruction_eq_zero_iff K n h i z).mpr
    rw [hz]
    rfl

/-- Killing this concrete map supplies the unchanged positive-order multiplication law. -/
theorem completeIdentityFiniteLaw_one_of_principalObstruction_zero
    (hz : completeIdentityFirstPrincipalObstruction K n h i = 0) :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  completeIdentityFiniteLaw_one_of_nodeObstruction_zero K n h i
    ((completeIdentityFirstPrincipalObstruction_zero_iff K n h i).mp hz)

end FLT.Mazur.PolygonInfinitesimalStages
