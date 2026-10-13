/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueEquality
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentPositiveEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResiduePositiveRetainedNodes
public import FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments

import all FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments
import all FLT.Mazur.WeierstrassCoefficientShearResiduePositiveRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueEquality

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Original equality terminal attachments at a positive level

The last retained pair needs only positive terminal level. This includes start
zero whenever s is positive, retaining the original full terminal parameter.
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

variable (hlevel : 0 < start + s)
local notation "C" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6 hc
local notation "N" => coefficientShearResiduePositiveRetainedNode
  hπ hm data s hs (Nat.le_of_eq he) h3 h4 ⟨s, by omega⟩ hlevel

include hlevel in
/-- The terminal zero is the last actual first retained node. -/
@[reassoc] theorem coefficientShearResidueEqualityComponent_zero_positive :
    ProjectiveLine.zero Q ≫ C = N 0 := by
  unfold coefficientShearResidueEqualityComponent
  rw [dite_eq_left hlevel, coefficientShearRootEqualityComponent_zero]
  exact coefficientShearRetainedFirstAttachment
    hπ data Q r (s + 1) hs ⟨s, by omega⟩
    (nodalDepth_tangent_scale_zero (W := W) hm hlevel)
    hp (lin).1 (lin).2 hr (Eq.mp (congrArg IsUnit ha) (Units.isUnit a))

include hlevel in
/-- The terminal infinity is the last actual opposite retained node. -/
@[reassoc] theorem coefficientShearResidueEqualityComponent_infinity_positive :
    ProjectiveLine.infinity Q ≫ C = N 1 := by
  unfold coefficientShearResidueEqualityComponent
  rw [dite_eq_left hlevel,
    coefficientShearRootEqualityComponent_infinity]
  exact coefficientShearRetainedSecondAttachment
    hπ data Q r (s + 1) hs ⟨s, by omega⟩
    (nodalDepth_tangent_scale_zero (W := W) hm hlevel)
    hp (lin).1 (lin).2 hr (Eq.mp (congrArg IsUnit ha) (Units.isUnit a))

local notation "A" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs (Nat.le_of_eq he) h3 h4 hc

/-- Consecutive complete adjacent components share the same original retained node. -/
theorem coefficientShearResidueAdjacentComponent_join (j : Fin s) (hj : j.val + 1 < s)
    (i : Fin 2) : ProjectiveLine.infinity Q ≫ A j i =
      ProjectiveLine.zero Q ≫ A ⟨j.val + 1, hj⟩ i := by
  rw [coefficientShearResidueAdjacentComponent_infinity_positive,
    coefficientShearResidueAdjacentComponent_zero_positive
      hπ hm data s hs (Nat.le_of_eq he) h3 h4 hc ⟨j.val + 1, hj⟩ (by dsimp; omega)]
  rfl

/-- The final first adjacent component attaches to the original terminal zero. -/
theorem coefficientShearResidueAdjacentComponent_equality_first (hspos : 0 < s) :
    ProjectiveLine.infinity Q ≫ A ⟨s - 1, by omega⟩ 0 = ProjectiveLine.zero Q ≫ C := by
  rw [coefficientShearResidueAdjacentComponent_infinity_positive,
    coefficientShearResidueEqualityComponent_zero_positive
      hπ hm data s hs he h3 h4 h6 hc (by omega)]
  have hi : (⟨s - 1, by omega⟩ : Fin s).succ = (⟨s, by omega⟩ : Fin (s + 1)) :=
    Fin.ext (by dsimp; omega)
  simp only [hi]

/-- The final opposite adjacent component attaches to the original terminal infinity. -/
theorem coefficientShearResidueAdjacentComponent_equality_second (hspos : 0 < s) :
    ProjectiveLine.infinity Q ≫ A ⟨s - 1, by omega⟩ 1 = ProjectiveLine.infinity Q ≫ C := by
  rw [coefficientShearResidueAdjacentComponent_infinity_positive,
    coefficientShearResidueEqualityComponent_infinity_positive
      hπ hm data s hs he h3 h4 h6 hc (by omega)]
  have hi : (⟨s - 1, by omega⟩ : Fin s).succ = (⟨s, by omega⟩ : Fin (s + 1)) :=
    Fin.ext (by dsimp; omega)
  simp only [hi]

end FLT.Mazur.WeierstrassDividedDepth
