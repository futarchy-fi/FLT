/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueBranches
public import FLT.Mazur.WeierstrassCoefficientShearResidueEquality
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLift
public import FLT.Mazur.PolygonPinchingDiagram

/-!
# The actual residue-tangent component coproduct in cyclic order

Assemble the complete ordered exterior, both independently constructed branches
and the independent equality terminal at one final stage. The coproduct retains
every full component and specializes to the actual integral tangent target.
Endpoint identifications and a pinching universal property are separate obligations.
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
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

/-- All complete residue components at the original positive-start cyclic positions. -/
def coefficientShearResidueCycleComponent (i : Fin (2 * s + 4)) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if i.val = 0 then F
  else if h : i.val ≤ s + 1 then ρ ≫ B ⟨i.val - 1, by omega⟩ 0
  else if ht : i.val = s + 2 then ρ ≫ T
  else B ⟨2 * s + 3 - i.val, by omega⟩ 1
local notation "C" => coefficientShearResidueCycleComponent
  hπ hm data s hs he hstart h3 h4 h6 h6next hc

/-- Every cyclic position preserves the full actual residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueCycleComponent_structure (i : Fin (2 * s + 4)) :
    C i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueCycleComponent
  split_ifs
  · exact coefficientShearResidueExteriorLift_structure ..
  · rw [Category.assoc, coefficientShearResidueBranchComponent_structure,
      ProjectiveLine.endpointReversal_toBase]
  · rw [Category.assoc, coefficientShearResidueEqualityComponent_structure,
      ProjectiveLine.endpointReversal_toBase]
  · exact coefficientShearResidueBranchComponent_structure ..

/-- The independently assembled complete cyclic components as actual maps over Q. -/
def coefficientShearResidueCycleOverComponent (i : Fin (2 * s + 4)) :
    PolygonPinching.component Q ⟶ Over.mk g :=
  Over.homMk (C i) (coefficientShearResidueCycleComponent_structure
    hπ hm data s hs he hstart h3 h4 h6 h6next hc i)

/-- The complete source coproduct maps into the actual residue-tangent final model. -/
def coefficientShearResidueCycleCoproduct :
    PolygonPinching.components Q (2 * s + 4) ⟶ Over.mk g :=
  Sigma.desc (coefficientShearResidueCycleOverComponent
    hπ hm data s hs he hstart h3 h4 h6 h6next hc)
local notation "N" => coefficientShearResidueCycleCoproduct
  hπ hm data s hs he hstart h3 h4 h6 h6next hc

/-- Every coproduct summand retains the full independently constructed component. -/
@[reassoc] theorem coefficientShearResidueCycleCoproduct_ι (i : Fin (2 * s + 4)) :
    (PolygonPinching.componentι Q (2 * s + 4) i).left ≫ (N).left = C i := by
  have h := Sigma.ι_comp_desc
    (coefficientShearResidueCycleOverComponent
      hπ hm data s hs he hstart h3 h4 h6 h6next hc) i
  exact congrArg (fun f => f.left) h

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- The full actual residue component coproduct specializes into the integral tangent target. -/
def coefficientShearIntegralCycleCoproduct :
    (PolygonPinching.components Q (2 * s + 4)).left ⟶
      coefficientShearGlued hπ data A rA (s + 1) hs := (N).left ≫ M

/-- Specialization preserves the full component at every original cyclic position. -/
@[reassoc] theorem coefficientShearIntegralCycleCoproduct_ι (i : Fin (2 * s + 4)) :
    (PolygonPinching.componentι Q (2 * s + 4) i).left ≫
        coefficientShearIntegralCycleCoproduct
          hπ hm data s hs he hstart h3 h4 h6 h6next hc = C i ≫ M := by
  rw [coefficientShearIntegralCycleCoproduct, coefficientShearResidueCycleCoproduct_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth
