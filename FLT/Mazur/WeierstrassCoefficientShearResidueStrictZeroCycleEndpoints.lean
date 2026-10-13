/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictBranchEndpoints
public import FLT.Mazur.PolygonOddChainEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroStrictTerminal
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAdjacentEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleCoproduct
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictBranches

/-!
# Every original endpoint in the zero-start strict-depth cycle

The full exterior and both complete chains satisfy all original cyclic node
equations, including the shared divided terminal node and the exterior wrap.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueStrictAdjacentBranch
  hπ hm data s hs hk h3 h4 h6 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueStrictZeroCycleComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

/-- Every original cyclic zero equals infinity on the next complete component. -/
theorem coefficientShearResidueStrictZeroCycleComponent_endpoints (i : Fin (2 * s + 3)) :
    ProjectiveLine.zero Q ≫ C i =
      ProjectiveLine.infinity Q ≫ C (PolygonPinching.next (by omega) i) := by
  apply PolygonPinching.oddChain_endpoints Q (2 * s + 3) s (by omega) F B C
  · exact coefficientShearResidueStrictZeroCycleComponent_exterior hπ hm data s hs hk h3 h4 h6 hc
  · exact coefficientShearResidueStrictZeroCycleComponent_first hπ hm data s hs hk h3 h4 h6 hc
  · exact coefficientShearResidueStrictZeroCycleComponent_second hπ hm data s hs hk h3 h4 h6 hc
  · by_cases hs0 : s = 0
    · subst s
      simp only [coefficientShearResidueStrictAdjacentBranch, Fin.val_zero,
        lt_self_iff_false, dite_false]
      exact (coefficientShearResidueZeroStrictTerminal_first
        hπ hm data hs hk h3 h4 h6 hc).symm
    · rw [coefficientShearResidueStrictAdjacentBranch,
        dite_eq_left (show (0 : Fin (s + 1)).val < s by dsimp; omega)]
      exact (coefficientShearResidueZeroAdjacent_first
        hπ hm data s hs (Nat.le_of_lt hk) h3 h4 hc (by omega)).symm
  · by_cases hs0 : s = 0
    · subst s
      simp only [coefficientShearResidueStrictAdjacentBranch, Fin.val_zero,
        lt_self_iff_false, dite_false]
      exact (coefficientShearResidueZeroStrictTerminal_second
        hπ hm data hs hk h3 h4 h6 hc)
    · rw [coefficientShearResidueStrictAdjacentBranch,
        dite_eq_left (show (0 : Fin (s + 1)).val < s by dsimp; omega)]
      exact (coefficientShearResidueZeroAdjacent_second
        hπ hm data s hs (Nat.le_of_lt hk) h3 h4 hc (by omega))
  · exact coefficientShearResidueStrictAdjacentBranch_endpoints hπ hm data s hs hk h3 h4 h6 hc
  · exact coefficientShearResidueStrictAdjacentBranch_final hπ hm data s hs hk h3 h4 h6 hc

end FLT.Mazur.WeierstrassDividedDepth
