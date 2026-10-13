/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeGluing
public import FLT.Mazur.WeierstrassCoefficientShearEqualityParameterCover
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameterCover
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeGluing

/-!
# Every full positive-index horizontal line of the start-zero descent

The original interior and equality charts retain both signed tangent parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueZeroGluedCoconeDesc
  hπ hm data s hs he h3 h4 h6next hc C
variable (i : Fin (s + 1)) (hipos : 0 < i.val)
local notation "d" => data ⟨i.val + 1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d
  (show 2 * (0 + (i.val + 1)) ≤ depth from by omega) h3 h4
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < 0 + i.val from by omega)
local notation "L" => coefficientShearRetainedLine hπ data Q r (s + 1) hs i
  hscale hp (lin).1 (lin).2 hr
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r

/-- Every positive-index first line recovers its preceding original cyclic component. -/
theorem coefficientShearResidueZeroGluedCoconeDesc_first_line :
    L 0 (middle_first_root U) ≫ M =
      ProjectiveLine.chartScaling Q a ≫ ProjectiveLine.left Q ≫ F ⟨i.val, by omega⟩ := by
  rw [coefficientShearRetainedLine, coefficientShearRetainedFiber]
  simp only [Category.assoc]
  rw [coefficientShearResidueZeroGluedCoconeDesc_chart,
    coefficientShearResidueZeroAtlasCoconeMap_retained]
  by_cases hi : i.val = s
  · have H : i = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hi
    subst i
    rw [coefficientShearResidueZeroRetainedCoconeMap_last
      hπ hm data s hs he h3 h4 h6next hc C hipos]
    exact coefficientShearResidueZeroLastDesc_first
      hπ hm data s hs he h3 h4 h6next hc hipos F w
  · erw [coefficientShearResidueZeroRetainedCoconeMap_interior
      hπ hm data s hs he h3 h4 h6next hc C ⟨i.val, by omega⟩ hipos]
    exact coefficientShearResidueZeroInteriorDesc_first_line
      hπ hm data s hs h3 h4 hc ⟨i.val, by omega⟩ hipos F w

/-- Every opposite full line keeps its negative scale and original cyclic position. -/
theorem coefficientShearResidueZeroGluedCoconeDesc_second_line :
    L (-(U).a₁) (middle_second_root U) ≫ M =
      ProjectiveLine.chartScaling Q (-a) ≫ ProjectiveLine.right Q ≫
        F ⟨2 * s + 2 - i.val, by omega⟩ := by
  rw [coefficientShearRetainedLine, coefficientShearRetainedFiber]
  simp only [Category.assoc]
  rw [coefficientShearResidueZeroGluedCoconeDesc_chart,
    coefficientShearResidueZeroAtlasCoconeMap_retained]
  by_cases hi : i.val = s
  · have H : i = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hi
    subst i
    rw [coefficientShearResidueZeroRetainedCoconeMap_last
      hπ hm data s hs he h3 h4 h6next hc C hipos]
    simpa only [coefficientShearRetainedEquationIso,
      show 2 * s + 2 - s = s + 2 from by omega] using
      coefficientShearResidueZeroLastDesc_second
        hπ hm data s hs he h3 h4 h6next hc hipos F w
  · erw [coefficientShearResidueZeroRetainedCoconeMap_interior
      hπ hm data s hs he h3 h4 h6next hc C ⟨i.val, by omega⟩ hipos]
    exact coefficientShearResidueZeroInteriorDesc_second_line
      hπ hm data s hs h3 h4 hc ⟨i.val, by omega⟩ hipos F w

end FLT.Mazur.WeierstrassDividedDepth
