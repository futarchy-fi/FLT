/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueEquality
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearResidueEquality
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityComponent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic

/-!
# The original two-component equality cycle at start zero

The original exterior and full scale-one equality terminal meet at both
original conic markings, without inserting an initial exceptional pair.
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
  (hs : 0 + 1 ≤ n) (he : 2 * (0 + (0 + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨0 + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6
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
local notation "C" => coefficientShearResidueEqualityComponent
  hπ hm data 0 hs he h3 h4 h6 hc

/-- The terminal zero is exactly the original exterior zero in the two-component case. -/
@[reassoc] theorem coefficientShearResidueZeroEquality_first :
    ProjectiveLine.zero Q ≫ C = ProjectiveLine.zero Q ≫ F := by
  unfold coefficientShearResidueEqualityComponent
  rw [dite_eq_right (by omega), coefficientShearScaleOneEqualityComponent_zero,
    coefficientShearResidueZeroExteriorLift_zero
      hπ data hs 0 hs hres (lin).1 (lin).2 a ha]

/-- The terminal infinity is exactly the original exterior infinity in the same original conic. -/
@[reassoc] theorem coefficientShearResidueZeroEquality_second :
    ProjectiveLine.infinity Q ≫ C = ProjectiveLine.infinity Q ≫ F := by
  unfold coefficientShearResidueEqualityComponent
  rw [dite_eq_right (by omega), coefficientShearScaleOneEqualityComponent_infinity,
    coefficientShearResidueZeroExteriorLift_infinity
      hπ data hs 0 hs hres (lin).1 (lin).2 a ha]

end FLT.Mazur.WeierstrassDividedDepth
