/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictBranchEndpoints
public import FLT.Mazur.PolygonOddChainEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorJunctions
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleCoproduct
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictBranches

/-!
# Every original endpoint in the positive-start strict-depth cycle

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
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueStrictPositiveBranch
  hπ hm data s hs hk h3 h4 h6 hc hstart
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueStrictPositiveCycleComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

/-- Every original cyclic zero equals infinity on the next complete component. -/
theorem coefficientShearResidueStrictPositiveCycleComponent_endpoints (i : Fin (2 * s + 5)) :
    ProjectiveLine.zero Q ≫ C i =
      ProjectiveLine.infinity Q ≫ C (PolygonPinching.next (by omega) i) := by
  apply PolygonPinching.oddChain_endpoints Q (2 * s + 5) (s + 1) (by omega) F B C
  · exact coefficientShearResidueStrictPositiveCycleComponent_exterior
      hπ hm data s hs hk hstart h3 h4 h6 hc
  · exact coefficientShearResidueStrictPositiveCycleComponent_first
      hπ hm data s hs hk hstart h3 h4 h6 hc
  · exact coefficientShearResidueStrictPositiveCycleComponent_second
      hπ hm data s hs hk hstart h3 h4 h6 hc
  · simp only [coefficientShearResidueStrictPositiveBranch, Fin.val_zero,
      Nat.zero_lt_succ, dite_true, coefficientShearResidueBranchComponent]
    exact (coefficientShearResidueExterior_initial_first
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc)
  · simp only [coefficientShearResidueStrictPositiveBranch, Fin.val_zero,
      Nat.zero_lt_succ, dite_true, coefficientShearResidueBranchComponent]
    exact (coefficientShearResidueExterior_initial_second
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc).symm
  · exact coefficientShearResidueStrictPositiveBranch_endpoints
      hπ hm data s hs hk h3 h4 h6 hc hstart
  · exact coefficientShearResidueStrictPositiveBranch_final hπ hm data s hs hk h3 h4 h6 hc hstart

end FLT.Mazur.WeierstrassDividedDepth
