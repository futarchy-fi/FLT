/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueEquality
public import FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
public import FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments

import all FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueEquality

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Actual positive-start equality terminal attachments

The completed terminal component meets the last actual retained node pair.
Its full parameter and its constant-scaled semilinear reciprocal are unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)

variable (hstart : 0 < start)
local notation "C" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6 hc
local notation "N" => coefficientShearResidueRetainedNode
  hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4 ⟨s, by omega⟩

include hstart in
/-- The terminal zero is the last actual first retained node. -/
@[reassoc] theorem coefficientShearResidueEqualityComponent_zero :
    ProjectiveLine.zero Q ≫ C = N 0 := by
  unfold coefficientShearResidueEqualityComponent
  rw [dite_eq_left (show 0 < start + s from by omega), coefficientShearRootEqualityComponent_zero]
  exact coefficientShearRetainedFirstAttachment
    hπ data Q r (s + 1) hs ⟨s, by omega⟩
    (nodalDepth_tangent_scale_zero (W := W) hm (by omega : 0 < start + s))
    hp (lin).1 (lin).2 hr (Eq.mp (congrArg IsUnit ha) (Units.isUnit a))

include hstart in
/-- The terminal infinity is the last actual opposite retained node. -/
@[reassoc] theorem coefficientShearResidueEqualityComponent_infinity :
    ProjectiveLine.infinity Q ≫ C = N 1 := by
  unfold coefficientShearResidueEqualityComponent
  rw [dite_eq_left (show 0 < start + s from by omega),
    coefficientShearRootEqualityComponent_infinity]
  exact coefficientShearRetainedSecondAttachment
    hπ data Q r (s + 1) hs ⟨s, by omega⟩
    (nodalDepth_tangent_scale_zero (W := W) hm (by omega : 0 < start + s))
    hp (lin).1 (lin).2 hr (Eq.mp (congrArg IsUnit ha) (Units.isUnit a))

end FLT.Mazur.WeierstrassDividedDepth
