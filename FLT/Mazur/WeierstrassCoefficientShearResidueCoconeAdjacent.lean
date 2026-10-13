/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeLines
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentLeftCharts
import all FLT.Mazur.WeierstrassCoefficientShearResidueInteriorDescent

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeLines

/-!
# Full projective restrictions on every original adjacent component pair

Every original adjacent pair retains both full affine charts and its cyclic orientation.
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
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs (Nat.le_of_eq he) h3 h4 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

/-- Every complete first adjacent component receives its reversed cyclic cocone map. -/
theorem coefficientShearResidueGluedCoconeDesc_adjacent_first (j : Fin s) :
    B j 0 ≫ M = ρ ≫ F ⟨j.val + 2, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ B j 0 ≫ M =
      ProjectiveLine.left Q ≫ ρ ≫ F ⟨j.val + 2, by omega⟩
    rw [ProjectiveLine.left_endpointReversal_assoc,
      coefficientShearResidueAdjacentComponent_first_left_assoc (hstart := hstart)]
    simp only [coefficientConicFirstParameter, coefficientShearRetainedConic,
      coefficientShearRetainedFiber, Category.assoc]
    rw [coefficientShearResidueGluedCoconeDesc_chart,
      coefficientShearResidueAtlasCoconeMap_interior]
    simpa only [coefficientShearRetainedEquationIso, Fin.val_castSucc, Category.assoc] using
      coefficientShearResidueInteriorDesc_first_conic
      hπ hm data s hs h3 h4 hc j hstart F w
  · change ProjectiveLine.right Q ≫ B j 0 ≫ M =
      ProjectiveLine.right Q ≫ ρ ≫ F ⟨j.val + 2, by omega⟩
    rw [ProjectiveLine.right_endpointReversal_assoc]
    have H := coefficientShearResidueGluedCoconeDesc_first_right
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C j.succ
    simpa only [Fin.succ, coefficientShearResidueBranchComponent_adjacent] using H

/-- Every opposite complete adjacent component keeps its independent cyclic position. -/
theorem coefficientShearResidueGluedCoconeDesc_adjacent_second (j : Fin s) :
    B j 1 ≫ M = F ⟨2 * s + 2 - j.val, by omega⟩ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left Q ≫ B j 1 ≫ M =
      ProjectiveLine.left Q ≫ F ⟨2 * s + 2 - j.val, by omega⟩
    rw [coefficientShearResidueAdjacentComponent_second_left_assoc (hstart := hstart)]
    simp only [coefficientConicSecondParameter, coefficientShearRetainedConic,
      coefficientShearRetainedFiber, Category.assoc]
    rw [coefficientShearResidueGluedCoconeDesc_chart,
      coefficientShearResidueAtlasCoconeMap_interior]
    simpa only [coefficientShearRetainedEquationIso, Fin.val_castSucc, Category.assoc] using
      coefficientShearResidueInteriorDesc_second_conic
      hπ hm data s hs h3 h4 hc j hstart F w
  · change ProjectiveLine.right Q ≫ B j 1 ≫ M =
      ProjectiveLine.right Q ≫ F ⟨2 * s + 2 - j.val, by omega⟩
    have H := coefficientShearResidueGluedCoconeDesc_second_right
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C j.succ
    simpa only [Fin.succ, coefficientShearResidueBranchComponent_adjacent,
      show 2 * s + 3 - (j.val + 1) = 2 * s + 2 - j.val from by omega] using H

end FLT.Mazur.WeierstrassDividedDepth
