/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeComponents
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeOver
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoproductHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeComponents
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCoconeOver

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
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 5) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 5) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueStrictPositiveGluedCoconeDesc
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "N" => coefficientShearResidueStrictPositiveCycleCoproduct
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "J" => coefficientShearResidueStrictPositiveCycleNodes
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "δ" => coefficientShearResidueStrictPositiveGluedCoconeOverDesc
  hπ hm data s hs hk hstart h3 h4 h6 hc C
local notation "P" => coefficientShearResidueStrictPositiveCyclePushoutCocone
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- The full original normalization coproduct factors through the actual Over descent. -/
theorem coefficientShearResidueStrictPositiveGluedCoconeOverDesc_components : N ≫ δ = C.inl := by
  apply Sigma.hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (PolygonPinching.componentι Q (2 * s + 5) i).left ≫ (N).left ≫ M = F i
  rw [coefficientShearResidueStrictPositiveCycleCoproduct_ι_assoc]
  exact coefficientShearResidueStrictPositiveGluedCoconeDesc_component
    hπ hm data s hs hk hstart h3 h4 h6 hc C i

/-- Every full original node summand factors through the same actual Over descent. -/
theorem coefficientShearResidueStrictPositiveGluedCoconeOverDesc_nodes : J ≫ δ = C.inr := by
  apply Sigma.hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (PolygonPinching.nodeι Q (2 * s + 5) i).left ≫ (J).left ≫ M =
    (PolygonPinching.nodeι Q (2 * s + 5) i ≫ C.inr).left
  rw [coefficientShearResidueStrictPositiveCycleNodes_ι_assoc,
    coefficientShearResidueStrictPositiveCycleNode,
    Category.assoc, coefficientShearResidueStrictPositiveGluedCoconeDesc_component]
  exact PolygonCyclicPushout.zero_input Q (2 * s + 5) (by omega)
    C.inl C.inr C.condition i

/-- The actual residue pinching cocone satisfies the full original universal property. -/
def coefficientShearResidueStrictPositiveCycleIsColimit : IsColimit P := by
  refine PushoutCocone.IsColimit.mk _
    (fun C => coefficientShearResidueStrictPositiveGluedCoconeOverDesc
      hπ hm data s hs hk hstart h3 h4 h6 hc C) ?_ ?_ ?_
  · intro C
    exact coefficientShearResidueStrictPositiveGluedCoconeOverDesc_components
      hπ hm data s hs hk hstart h3 h4 h6 hc C
  · intro C
    exact coefficientShearResidueStrictPositiveGluedCoconeOverDesc_nodes
      hπ hm data s hs hk hstart h3 h4 h6 hc C
  · intro C f hf _
    apply coefficientShearResidueStrictPositiveCycleOver_hom_ext
      hπ hm data s hs hk hstart h3 h4 h6 hc f
    exact hf.trans (coefficientShearResidueStrictPositiveGluedCoconeOverDesc_components
      hπ hm data s hs hk hstart h3 h4 h6 hc C).symm

/-- The given normalization and node maps form the original pushout square over Q. -/
theorem coefficientShearResidueStrictPositiveCycle_isPushout :
    IsPushout (PolygonPinching.toComponents Q (2 * s + 5) (by omega))
      (PolygonPinching.toNodes Q (2 * s + 5)) N J :=
  ⟨⟨coefficientShearResidueStrictPositiveCycleCoproduct_cocone
    hπ hm data s hs hk hstart h3 h4 h6 hc⟩,
    ⟨coefficientShearResidueStrictPositiveCycleIsColimit
      hπ hm data s hs hk hstart h3 h4 h6 hc⟩⟩

end FLT.Mazur.WeierstrassDividedDepth
