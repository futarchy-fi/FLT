/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearTerminalEquationCharts
public import FLT.Mazur.PolygonCyclicPushout

/-!
# Strict odd cyclic descent to the entire original divided equation

The two middle cyclic inputs descend along the actual opposite terminal branches.
The cycle length and terminal position are explicit, covering both starts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
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
local notation "B₁" => coefficientShearTerminalEquationFirst
  data Q r (s + 1) hs hscale (lin).1 (lin).2 g6 hr a ha
local notation "B₂" => coefficientShearTerminalEquationSecond
  data Q r (s + 1) hs hscale (lin).1 (lin).2 g6 hr a ha
variable (m N : ℕ) (hN : m + 2 < N) {Y : Scheme}
  (F : Fin N → (ProjectiveLine.scheme
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫ F i =
      ProjectiveLine.infinity (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫
        F (PolygonPinching.next (by omega) i))

/-- The entire divided equation receives the two middle cyclic charts in their actual order. -/
@[irreducible] def coefficientShearResidueStrictDividedDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 1) ⟶ Y :=
  coefficientShearTerminalEquationDesc data Q r (s + 1) hs hscale
    (lin).1 (lin).2 g6 hr a ha
    (ProjectiveLine.right Q ≫ F ⟨m + 2, by omega⟩)
    (ProjectiveLine.left Q ≫ F ⟨m + 1, by omega⟩)
    (by
      have hn : PolygonPinching.next (by omega)
          (⟨m + 1, by omega⟩ : Fin N) = ⟨m + 2, by omega⟩ := by
        apply Fin.ext
        change (m + 1 + 1) % N = m + 2
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [hn, ProjectiveLine.zero, ProjectiveLine.infinity, Category.assoc] using
        (w ⟨m + 1, by omega⟩).symm)
local notation "D" => coefficientShearResidueStrictDividedDesc
  hπ hm data s hs hk h3 h4 h6 hc m N hN F w

/-- The first actual terminal branch receives the second middle component's right chart. -/
@[reassoc] theorem coefficientShearResidueStrictDividedDesc_first :
    B₁ ≫ D = ProjectiveLine.right Q ≫ F ⟨m + 2, by omega⟩ := by
  rw [coefficientShearResidueStrictDividedDesc, coefficientShearTerminalEquationDesc_first]

/-- The opposite actual branch receives the reversed first middle component's left chart. -/
@[reassoc] theorem coefficientShearResidueStrictDividedDesc_second :
    B₂ ≫ D = ProjectiveLine.left Q ≫ F ⟨m + 1, by omega⟩ := by
  rw [coefficientShearResidueStrictDividedDesc, coefficientShearTerminalEquationDesc_second]

/-- The full original branch restrictions uniquely characterize this terminal descent. -/
theorem coefficientShearResidueStrictDividedDesc_unique
    (f : coefficientShearAtlasObject data Q r (s + 1) hs (.inl 1) ⟶ Y)
    (h₁ : B₁ ≫ f = ProjectiveLine.right Q ≫ F ⟨m + 2, by omega⟩)
    (h₂ : B₂ ≫ f = ProjectiveLine.left Q ≫ F ⟨m + 1, by omega⟩) : f = D := by
  apply coefficientShearTerminalEquation_hom_ext
    data Q r (s + 1) hs hscale (lin).1 (lin).2 g6 hr a ha
  · exact h₁.trans (coefficientShearResidueStrictDividedDesc_first
      hπ hm data s hs hk h3 h4 h6 hc m N hN F w).symm
  · exact h₂.trans (coefficientShearResidueStrictDividedDesc_second
      hπ hm data s hs hk h3 h4 h6 hc m N hN F w).symm

/-- Over-base input components give an over-base map on the entire divided equation. -/
theorem coefficientShearResidueStrictDividedDesc_structure
    (b : Y ⟶ Spec (.of Q)) (hb : ∀ i, F i ≫ b = ProjectiveLine.toBase Q) :
    D ≫ b = coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 1) := by
  rw [coefficientShearResidueStrictDividedDesc]
  apply coefficientShearTerminalEquationDesc_structure
  · rw [Category.assoc, hb, ProjectiveLine.right_toBase]
  · rw [Category.assoc, hb, ProjectiveLine.left_toBase]

end FLT.Mazur.WeierstrassDividedDepth
