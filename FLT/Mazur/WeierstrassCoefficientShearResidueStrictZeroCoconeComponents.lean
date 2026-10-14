/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeExterior
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeFullBranches
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleCoproduct
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeExterior
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeFullBranches

/-!
# Every original cyclic component factors through the actual cocone descent

All full components retain their specified cyclic positions and orientations.
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
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 3) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictZeroAtlasCoconeMap
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueStrictZeroGluedCoconeDesc
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "B" => coefficientShearResidueStrictZeroCycleComponent
  hπ hm data s hs hk h3 h4 h6 hc

/-- The actual descended morphism recovers every full original cyclic component. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_component (i : Fin (2 * s + 3)) :
    B i ≫ M = F i := by
  rw [coefficientShearResidueStrictZeroCycleComponent]
  split_ifs with hz hb
  · have hi : i = 0 := Fin.ext hz
    subst i
    exact coefficientShearResidueStrictZeroGluedCoconeDesc_exterior
      hπ hm data s hs hk h3 h4 h6 hc C
  · rw [Category.assoc, coefficientShearResidueStrictZeroGluedCoconeDesc_full_branch_first,
      ← Category.assoc, ProjectiveLine.endpointReversal_involutive, Category.id_comp]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · rw [coefficientShearResidueStrictZeroGluedCoconeDesc_full_branch_second]
    congr 1
    apply Fin.ext
    dsimp
    omega

end FLT.Mazur.WeierstrassDividedDepth
