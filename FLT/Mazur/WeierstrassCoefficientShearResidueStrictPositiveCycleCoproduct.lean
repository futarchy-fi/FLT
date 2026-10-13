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
# Full original positive-start component coproduct at strict depth

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

/-- All complete residue components at the original positive-start strict-depth positions. -/
def coefficientShearResidueStrictPositiveCycleComponent (i : Fin (2 * s + 5)) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if i.val = 0 then F
  else if h : i.val ≤ s + 2 then ρ ≫ B ⟨i.val - 1, by omega⟩ 0
  else B ⟨2 * s + 4 - i.val, by omega⟩ 1
local notation "C" => coefficientShearResidueStrictPositiveCycleComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- Every cyclic position preserves the full actual residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleComponent_structure
    (i : Fin (2 * s + 5)) :
    C i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueStrictPositiveCycleComponent
  split_ifs
  · exact coefficientShearResidueExteriorLift_structure ..
  · rw [Category.assoc, coefficientShearResidueStrictPositiveBranch_structure,
      ProjectiveLine.endpointReversal_toBase]
  · exact coefficientShearResidueStrictPositiveBranch_structure ..

/-- The independently assembled complete cyclic components as actual maps over Q. -/
def coefficientShearResidueStrictPositiveCycleOverComponent (i : Fin (2 * s + 5)) :
    PolygonPinching.component Q ⟶ Over.mk g :=
  Over.homMk (C i) (coefficientShearResidueStrictPositiveCycleComponent_structure
    hπ hm data s hs hk hstart h3 h4 h6 hc i)

/-- The complete source coproduct maps into the actual residue-tangent final model. -/
def coefficientShearResidueStrictPositiveCycleCoproduct :
    PolygonPinching.components Q (2 * s + 5) ⟶ Over.mk g :=
  Sigma.desc (coefficientShearResidueStrictPositiveCycleOverComponent
    hπ hm data s hs hk hstart h3 h4 h6 hc)
local notation "N" => coefficientShearResidueStrictPositiveCycleCoproduct
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- Every coproduct summand retains the full independently constructed component. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleCoproduct_ι (i : Fin (2 * s + 5)) :
    (PolygonPinching.componentι Q (2 * s + 5) i).left ≫ (N).left = C i := by
  have h := Sigma.ι_comp_desc
    (coefficientShearResidueStrictPositiveCycleOverComponent
      hπ hm data s hs hk hstart h3 h4 h6 hc) i
  exact congrArg (fun f => f.left) h

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- The full actual residue component coproduct specializes into the integral tangent target. -/
def coefficientShearIntegralStrictPositiveCycleCoproduct :
    (PolygonPinching.components Q (2 * s + 5)).left ⟶
      coefficientShearGlued hπ data A rA (s + 1) hs := (N).left ≫ M

/-- Specialization preserves the full component at every original cyclic position. -/
@[reassoc] theorem coefficientShearIntegralStrictPositiveCycleCoproduct_ι (i : Fin (2 * s + 5)) :
    (PolygonPinching.componentι Q (2 * s + 5) i).left ≫
        coefficientShearIntegralStrictPositiveCycleCoproduct
          hπ hm data s hs hk hstart h3 h4 h6 hc = C i ≫ M := by
  rw [coefficientShearIntegralStrictPositiveCycleCoproduct,
    coefficientShearResidueStrictPositiveCycleCoproduct_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth
