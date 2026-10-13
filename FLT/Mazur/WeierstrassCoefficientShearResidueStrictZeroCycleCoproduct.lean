/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictBranches
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLift
public import FLT.Mazur.PolygonPinchingDiagram

/-!
# Full original zero-start component coproduct at strict depth

The original exterior closes the two complete branches, including their
independent terminal components. This constructs the actual component maps;
the endpoint equations and universal property remain separate obligations.
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

/-- All complete residue components at the original start-zero strict-depth positions. -/
def coefficientShearResidueStrictZeroCycleComponent (i : Fin (2 * s + 3)) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if h0 : i.val = 0 then F
  else if h : i.val ≤ s + 1 then ρ ≫ B ⟨i.val - 1, by omega⟩ 0
  else B ⟨2 * s + 2 - i.val, by omega⟩ 1
local notation "C" => coefficientShearResidueStrictZeroCycleComponent
  hπ hm data s hs hk h3 h4 h6 hc

/-- Every cyclic position preserves the full actual residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleComponent_structure (i :
    Fin (2 * s + 3)) :
    C i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueStrictZeroCycleComponent
  split_ifs
  · exact coefficientShearResidueExteriorLift_structure ..
  · rw [Category.assoc, coefficientShearResidueStrictAdjacentBranch_structure,
      ProjectiveLine.endpointReversal_toBase]
  · exact coefficientShearResidueStrictAdjacentBranch_structure ..

/-- The independently assembled complete cyclic components as actual maps over Q. -/
def coefficientShearResidueStrictZeroCycleOverComponent (i : Fin (2 * s + 3)) :
    PolygonPinching.component Q ⟶ Over.mk g :=
  Over.homMk (C i) (coefficientShearResidueStrictZeroCycleComponent_structure
    hπ hm data s hs hk h3 h4 h6 hc i)

/-- The complete source coproduct maps into the actual residue-tangent final model. -/
def coefficientShearResidueStrictZeroCycleCoproduct :
    PolygonPinching.components Q (2 * s + 3) ⟶ Over.mk g :=
  Sigma.desc (coefficientShearResidueStrictZeroCycleOverComponent
    hπ hm data s hs hk h3 h4 h6 hc)
local notation "N" => coefficientShearResidueStrictZeroCycleCoproduct
  hπ hm data s hs hk h3 h4 h6 hc

/-- Every coproduct summand retains the full independently constructed component. -/
@[reassoc] theorem coefficientShearResidueStrictZeroCycleCoproduct_ι (i : Fin (2 * s + 3)) :
    (PolygonPinching.componentι Q (2 * s + 3) i).left ≫ (N).left = C i := by
  have h := Sigma.ι_comp_desc
    (coefficientShearResidueStrictZeroCycleOverComponent
      hπ hm data s hs hk h3 h4 h6 hc) i
  exact congrArg (fun f => f.left) h

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- The full actual residue component coproduct specializes into the integral tangent target. -/
def coefficientShearIntegralStrictZeroCycleCoproduct :
    (PolygonPinching.components Q (2 * s + 3)).left ⟶
      coefficientShearGlued hπ data A rA (s + 1) hs := (N).left ≫ M

/-- Specialization preserves the full component at every original cyclic position. -/
@[reassoc] theorem coefficientShearIntegralStrictZeroCycleCoproduct_ι (i : Fin (2 * s + 3)) :
    (PolygonPinching.componentι Q (2 * s + 3) i).left ≫
        coefficientShearIntegralStrictZeroCycleCoproduct
          hπ hm data s hs hk h3 h4 h6 hc = C i ≫ M := by
  rw [coefficientShearIntegralStrictZeroCycleCoproduct,
    coefficientShearResidueStrictZeroCycleCoproduct_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth
