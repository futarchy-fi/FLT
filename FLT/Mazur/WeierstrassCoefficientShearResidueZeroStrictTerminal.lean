/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueTerminalEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminal
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearRootTerminalZeroComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic

/-!
# The original three-component strict cycle at start zero

Both independent scale-one terminal components attach to the actual exterior
at their original zero markings. Their infinities meet at the divided node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hs : 0 + 1 ≤ n) (hk : 2 * (0 + (0 + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨0 + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_lt hk) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d hk h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "g" => coefficientShearGluedStructure hπ data Q r (0 + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (0 + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)

local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift
  hπ data (0 + 1) hs d (by dsimp; omega) hres a
local notation "C" => coefficientShearResidueTerminalComponent
  hπ hm data 0 hs hk h3 h4 h6 hc

/-- The first terminal zero is the original exterior zero when no adjacent pair remains. -/
@[reassoc] theorem coefficientShearResidueZeroStrictTerminal_first :
    ProjectiveLine.zero Q ≫ C 0 = ProjectiveLine.zero Q ≫ F := by
  unfold coefficientShearResidueTerminalComponent
  rw [dite_eq_right (by omega), ite_eq_left rfl,
    coefficientShearRootTerminalZeroFirstComponent_zero,
    coefficientConicFirstParameter_affine_origin,
    coefficientShearResidueZeroExteriorLift_zero
      hπ data hs 0 hs hres (lin).1 (lin).2 a ha]

/-- The opposite terminal zero attaches to the original exterior infinity. -/
@[reassoc] theorem coefficientShearResidueZeroStrictTerminal_second :
    ProjectiveLine.zero Q ≫ C 1 = ProjectiveLine.infinity Q ≫ F := by
  unfold coefficientShearResidueTerminalComponent
  rw [dite_eq_right (by omega), ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
    coefficientShearRootTerminalZeroSecondComponent_zero,
    coefficientConicSecondParameter_affine_origin,
    coefficientShearResidueZeroExteriorLift_infinity
      hπ data hs 0 hs hres (lin).1 (lin).2 a ha]

end FLT.Mazur.WeierstrassDividedDepth
