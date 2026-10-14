/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueTerminal
public import FLT.Mazur.WeierstrassCoefficientShearTerminalEquationCharts

/-!
# The actual strict terminal components detect the divided equation

Both scale cases retain the full, oppositely ordered affine terminal branches.
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
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + (s + 1) from by omega)
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "B₁" => coefficientShearTerminalFirstBranch
  hπ data Q r (s + 1) hs hscale (lin).1 (lin).2 g6 hr a ha
local notation "B₂" => coefficientShearTerminalSecondBranch
  hπ data Q r (s + 1) hs hscale (lin).1 (lin).2 g6 hr a ha

/-- The full first terminal component has the original opposite affine branch on the right. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_first_right :
    ProjectiveLine.right Q ≫ T 0 = B₂ := by
  unfold coefficientShearResidueTerminalComponent
  by_cases h : 0 < start + s
  · rw [dite_eq_left h, ite_eq_left rfl,
      coefficientShearRootTerminalFirstComponent_right]
  · rw [dite_eq_right h, ite_eq_left rfl,
      coefficientShearRootTerminalZeroFirstComponent_right]

/-- The opposite full terminal component has the original first affine branch on the right. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_second_right :
    ProjectiveLine.right Q ≫ T 1 = B₁ := by
  unfold coefficientShearResidueTerminalComponent
  by_cases h : 0 < start + s
  · rw [dite_eq_left h, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
      coefficientShearRootTerminalSecondComponent_right]
  · rw [dite_eq_right h, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
      coefficientShearRootTerminalZeroSecondComponent_right]

/-- Agreement on both whole terminal components detects the full original divided chart. -/
theorem coefficientShearResidueStrictDivided_hom_ext {Y : Scheme}
    (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (h₀ : T 0 ≫ u = T 0 ≫ v) (h₁ : T 1 ≫ u = T 1 ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 1) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 1) ≫ v := by
  apply coefficientShearTerminalEquation_hom_ext
    data Q r (s + 1) hs hscale (lin).1 (lin).2 g6 hr a ha
  · have h := congrArg (fun f => ProjectiveLine.right Q ≫ f) h₁
    simpa only [coefficientShearTerminalEquationFirst_chart_assoc,
      coefficientShearResidueTerminalComponent_second_right_assoc] using h
  · have h := congrArg (fun f => ProjectiveLine.right Q ≫ f) h₀
    simpa only [coefficientShearTerminalEquationSecond_chart_assoc,
      coefficientShearResidueTerminalComponent_first_right_assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
