/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueTerminal
public import FLT.Mazur.WeierstrassCoefficientShearConicOrigins
public import FLT.Mazur.WeierstrassCoefficientShearResiduePositiveRetainedNodes
public import FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminal
import all FLT.Mazur.WeierstrassCoefficientShearRetainedAttachments
import all FLT.Mazur.WeierstrassCoefficientShearResiduePositiveRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# The original terminal pair meets at the actual divided node

Both complete terminal components share their infinity section. At positive
terminal level their zero sections are precisely the two retained node sections.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm e hk h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

local notation "C" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "hsNext" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + (s + 1) by omega)
local notation "O" => coefficientShearTerminalOrigin
  hπ data Q r (s + 1) hs hsNext (lin).1 (lin).2 g6 hr a ha

/-- Every full terminal component ends at the same actual divided origin. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_infinity (i : Fin 2) :
    ProjectiveLine.infinity Q ≫ C i = O := by
  unfold coefficientShearResidueTerminalComponent
  split_ifs
  · exact coefficientShearRootTerminalFirstComponent_infinity ..
  · exact coefficientShearRootTerminalSecondComponent_infinity ..
  · exact coefficientShearRootTerminalZeroFirstComponent_infinity ..
  · exact coefficientShearRootTerminalZeroSecondComponent_infinity ..

/-- The two full terminal projective components meet at their infinity markings. -/
theorem coefficientShearResidueTerminalComponent_join :
    ProjectiveLine.infinity Q ≫ C 0 = ProjectiveLine.infinity Q ≫ C 1 := by
  rw [coefficientShearResidueTerminalComponent_infinity,
    coefficientShearResidueTerminalComponent_infinity]

variable (hlevel : 0 < start + s)
local notation "N" => coefficientShearResiduePositiveRetainedNode
  hπ hm data s hs (Nat.le_of_lt hk) h3 h4 ⟨s, by omega⟩ hlevel

/-- Each full terminal zero is the preceding retained node with its original branch index. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_zero_positive (i : Fin 2) :
    ProjectiveLine.zero Q ≫ C i = N i := by
  unfold coefficientShearResidueTerminalComponent
  rw [dite_eq_left hlevel]
  fin_cases i
  · simp only [Fin.ext_iff, Fin.val_zero, ↓reduceIte]
    rw [coefficientShearRootTerminalFirstComponent_zero,
      coefficientConicFirstParameter_affine_origin]
    exact coefficientShearRetainedFirstAttachment
      hπ data Q r (s + 1) hs ⟨s, by omega⟩
      (nodalDepth_tangent_scale_zero (W := W) hm hlevel)
      hp (lin).1 (lin).2 hr (Eq.mp (congrArg IsUnit ha) (Units.isUnit a))
  · simp only [Fin.ext_iff, Fin.val_zero, Nat.one_ne_zero, ↓reduceIte]
    rw [coefficientShearRootTerminalSecondComponent_zero,
      coefficientConicSecondParameter_affine_origin]
    exact coefficientShearRetainedSecondAttachment
      hπ data Q r (s + 1) hs ⟨s, by omega⟩
      (nodalDepth_tangent_scale_zero (W := W) hm hlevel)
      hp (lin).1 (lin).2 hr (Eq.mp (congrArg IsUnit ha) (Units.isUnit a))

end FLT.Mazur.WeierstrassDividedDepth
