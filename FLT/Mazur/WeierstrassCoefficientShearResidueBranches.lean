/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueInitial
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent

/-!
# Actual residue-tangent branches at the common final stage

Assemble the independently constructed initial and adjacent pairs in the original
branch order. Conjugation exchanges whole branches without changing their levels,
and specialization carries them into the original integral tangent model.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "C₀" => coefficientShearResidueInitialComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "C₁" => coefficientShearResidueAdjacentComponent hπ hm data s hs hk h3 h4 hc

/-- Both full branches retain their initial position and every subsequent retained level. -/
def coefficientShearResidueBranchComponent (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if h : j.val = 0 then C₀ i else C₁ ⟨j.val - 1, by omega⟩ i
local notation "C" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- The first position is the independent complete initial pair. -/
theorem coefficientShearResidueBranchComponent_initial (i : Fin 2) : C 0 i = C₀ i := by
  simp only [coefficientShearResidueBranchComponent, Fin.val_zero, dite_true]

/-- A subsequent position retains the actual adjacent pair with no level shift. -/
theorem coefficientShearResidueBranchComponent_adjacent (j : Fin s) (i : Fin 2) :
    C ⟨j.val + 1, by omega⟩ i = C₁ j i := by
  rw [coefficientShearResidueBranchComponent, dite_eq_right (by omega : ¬j.val + 1 = 0)]
  rfl

/-- Every branch position is a complete morphism over the actual residue coefficient field. -/
@[reassoc] theorem coefficientShearResidueBranchComponent_structure (j : Fin (s + 1)) (i : Fin 2) :
    C j i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueBranchComponent
  split_ifs
  · exact coefficientShearResidueInitialComponent_structure ..
  · exact coefficientShearResidueAdjacentComponent_structure ..

/-- Full actual residue conjugation exchanges the two branches at each original level. -/
@[reassoc] theorem coefficientShearResidueBranchComponent_conjugation
    (j : Fin (s + 1)) (i : Fin 2) : C j i ≫ σ = P ≫ C j i.rev := by
  unfold coefficientShearResidueBranchComponent
  split_ifs
  · exact coefficientShearResidueInitialComponent_conjugation ..
  · exact coefficientShearResidueAdjacentComponent_conjugation ..

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- Both full branches specialize into the same actual integral tangent target. -/
def coefficientShearIntegralBranchComponent (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data A rA (s + 1) hs := C j i ≫ M
local notation "I" => coefficientShearIntegralBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- The full specialized branch exchange is the actual integral conjugation. -/
@[reassoc] theorem coefficientShearIntegralBranchComponent_conjugation
    (j : Fin (s + 1)) (i : Fin 2) :
    I j i ≫ coefficientShearTangentConjugation hπ data (s + 1) hs = P ≫ I j i.rev := by
  simp only [coefficientShearIntegralBranchComponent, Category.assoc]
  rw [← coefficientShearTangentSpecialization_conjugation, ← Category.assoc,
    coefficientShearResidueBranchComponent_conjugation]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
