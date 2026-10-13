/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing
public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasLines
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing

/-!
# Full retained line restrictions of the original glued cocone descent

Full pullback compatibility constructs a morphism on the actual coefficient
model and its equation gluing. Every entire original chart is retained.
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
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 4) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 4) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueAtlasCoconeMap
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueGluedCoconeDesc
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C
local notation "L" => coefficientShearResidueRetainedPair
  hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4 h6 hc

/-- The glued map retains every entire first horizontal line with its original scale. -/
theorem coefficientShearResidueGluedCoconeDesc_first_line (j : Fin (s + 1)) :
    L j 0 ≫ M = ProjectiveLine.chartScaling Q a ≫ ProjectiveLine.left Q ≫
      F ⟨j.val + 1, by omega⟩ := by
  rw [coefficientShearResidueRetainedPair, ite_eq_left rfl,
    coefficientShearRetainedLine, coefficientShearRetainedFiber]
  simp only [Category.assoc]
  rw [coefficientShearResidueGluedCoconeDesc_chart]
  exact coefficientShearResidueAtlasCoconeMap_first_line
    hπ hm data s hs he hstart h3 h4 h6 h6next hc C j

/-- The opposite entire retained line keeps the negative original tangent scale. -/
theorem coefficientShearResidueGluedCoconeDesc_second_line (j : Fin (s + 1)) :
    L j 1 ≫ M = ProjectiveLine.chartScaling Q (-a) ≫ ProjectiveLine.right Q ≫
      F ⟨2 * s + 3 - j.val, by omega⟩ := by
  rw [coefficientShearResidueRetainedPair,
    ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide),
    coefficientShearRetainedLine, coefficientShearRetainedFiber]
  simp only [Category.assoc]
  rw [coefficientShearResidueGluedCoconeDesc_chart]
  exact coefficientShearResidueAtlasCoconeMap_second_line
    hπ hm data s hs he hstart h3 h4 h6 h6next hc C j

/-- The whole first branch right chart recovers the original cyclic component chart. -/
theorem coefficientShearResidueGluedCoconeDesc_first_right (j : Fin (s + 1)) :
    ProjectiveLine.right Q ≫ B j 0 ≫ M =
      ProjectiveLine.left Q ≫ F ⟨j.val + 1, by omega⟩ := by
  rw [coefficientShearResidueBranchComponent_right_assoc]
  simp only [ite_true]
  rw [coefficientShearResidueGluedCoconeDesc_first_line,
    ← Category.assoc, ← ProjectiveLine.chartScaling_mul]
  simp only [inv_mul_cancel, ProjectiveLine.chartScaling_one, Category.id_comp]

/-- The whole opposite branch right chart recovers its original cyclic component chart. -/
theorem coefficientShearResidueGluedCoconeDesc_second_right (j : Fin (s + 1)) :
    ProjectiveLine.right Q ≫ B j 1 ≫ M =
      ProjectiveLine.right Q ≫ F ⟨2 * s + 3 - j.val, by omega⟩ := by
  rw [coefficientShearResidueBranchComponent_right_assoc]
  rw [ite_eq_right (show (1 : Fin 2) ≠ 0 from by decide),
    coefficientShearResidueGluedCoconeDesc_second_line,
    ← Category.assoc, ← ProjectiveLine.chartScaling_mul]
  simp only [inv_mul_cancel, ProjectiveLine.chartScaling_one, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
