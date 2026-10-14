/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeComponents
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeOver
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoproductHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCycleNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeComponents
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeOver

/-!
# The full original residue pinching cocone is a colimit

The actual equation gluing satisfies the universal property for arbitrary targets
in the original coefficient slice, retaining all component and node maps.
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
local notation "N" => coefficientShearResidueStrictZeroCycleCoproduct
  hπ hm data s hs hk h3 h4 h6 hc
local notation "J" => coefficientShearResidueStrictZeroCycleNodes
  hπ hm data s hs hk h3 h4 h6 hc
local notation "δ" => coefficientShearResidueStrictZeroGluedCoconeOverDesc
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "P" => coefficientShearResidueStrictZeroCyclePushoutCocone
  hπ hm data s hs hk h3 h4 h6 hc

/-- The full original normalization coproduct factors through the actual Over descent. -/
theorem coefficientShearResidueStrictZeroGluedCoconeOverDesc_components : N ≫ δ = C.inl := by
  apply Sigma.hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (PolygonPinching.componentι Q (2 * s + 3) i).left ≫ (N).left ≫ M = F i
  rw [coefficientShearResidueStrictZeroCycleCoproduct_ι_assoc]
  exact coefficientShearResidueStrictZeroGluedCoconeDesc_component
    hπ hm data s hs hk h3 h4 h6 hc C i

/-- Every full original node summand factors through the same actual Over descent. -/
theorem coefficientShearResidueStrictZeroGluedCoconeOverDesc_nodes : J ≫ δ = C.inr := by
  apply Sigma.hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (PolygonPinching.nodeι Q (2 * s + 3) i).left ≫ (J).left ≫ M =
    (PolygonPinching.nodeι Q (2 * s + 3) i ≫ C.inr).left
  rw [coefficientShearResidueStrictZeroCycleNodes_ι_assoc,
    coefficientShearResidueStrictZeroCycleNode,
    Category.assoc, coefficientShearResidueStrictZeroGluedCoconeDesc_component]
  exact PolygonCyclicPushout.zero_input Q (2 * s + 3) (by omega)
    C.inl C.inr C.condition i

/-- The actual residue pinching cocone satisfies the full original universal property. -/
def coefficientShearResidueStrictZeroCycleIsColimit : IsColimit P := by
  refine PushoutCocone.IsColimit.mk _
    (fun C => coefficientShearResidueStrictZeroGluedCoconeOverDesc
      hπ hm data s hs hk h3 h4 h6 hc C) ?_ ?_ ?_
  · intro C
    exact coefficientShearResidueStrictZeroGluedCoconeOverDesc_components
      hπ hm data s hs hk h3 h4 h6 hc C
  · intro C
    exact coefficientShearResidueStrictZeroGluedCoconeOverDesc_nodes
      hπ hm data s hs hk h3 h4 h6 hc C
  · intro C f hf _
    apply coefficientShearResidueStrictZeroCycleOver_hom_ext
      hπ hm data s hs hk h3 h4 h6 hc f
    exact hf.trans (coefficientShearResidueStrictZeroGluedCoconeOverDesc_components
      hπ hm data s hs hk h3 h4 h6 hc C).symm

/-- The given normalization and node maps form the original pushout square over Q. -/
theorem coefficientShearResidueStrictZeroCycle_isPushout :
    IsPushout (PolygonPinching.toComponents Q (2 * s + 3) (by omega))
      (PolygonPinching.toNodes Q (2 * s + 3)) N J :=
  ⟨⟨coefficientShearResidueStrictZeroCycleCoproduct_cocone
    hπ hm data s hs hk h3 h4 h6 hc⟩,
    ⟨coefficientShearResidueStrictZeroCycleIsColimit
      hπ hm data s hs hk h3 h4 h6 hc⟩⟩

end FLT.Mazur.WeierstrassDividedDepth
