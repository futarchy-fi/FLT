/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeInitial
public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueInitial
import all FLT.Mazur.WeierstrassCoefficientShearResidueInitialCharts
import all FLT.Mazur.WeierstrassCoefficientShearResidueInitialCoconeDescent

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeLines

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeInitial
import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeAdjacent

/-!
# Every complete original branch recovers the corresponding cocone component

Combine the initial and adjacent restrictions with the unchanged branch indexing.
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
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4 h6 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

/-- Every whole first branch retains its original reversed cyclic position. -/
theorem coefficientShearResidueGluedCoconeDesc_branch_first (j : Fin (s + 1)) :
    B j 0 ≫ M = ρ ≫ F ⟨j.val + 1, by omega⟩ := by
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [coefficientShearResidueBranchComponent_initial]
    exact coefficientShearResidueGluedCoconeDesc_initial_first
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C
  · simpa only [Fin.succ, coefficientShearResidueBranchComponent_adjacent,
      Nat.add_assoc] using coefficientShearResidueGluedCoconeDesc_adjacent_first
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C k

/-- Every whole opposite branch retains the independent opposite cyclic position. -/
theorem coefficientShearResidueGluedCoconeDesc_branch_second (j : Fin (s + 1)) :
    B j 1 ≫ M = F ⟨2 * s + 3 - j.val, by omega⟩ := by
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [coefficientShearResidueBranchComponent_initial]
    exact coefficientShearResidueGluedCoconeDesc_initial_second
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C
  · simpa only [Fin.succ, coefficientShearResidueBranchComponent_adjacent,
      show 2 * s + 3 - (k.val + 1) = 2 * s + 2 - k.val from by omega] using
      coefficientShearResidueGluedCoconeDesc_adjacent_second
        hπ hm data s hs he hstart h3 h4 h6 h6next hc C k

end FLT.Mazur.WeierstrassDividedDepth
