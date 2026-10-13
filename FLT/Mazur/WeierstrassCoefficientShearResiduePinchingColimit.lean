/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeComponents
public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeOver
public import FLT.Mazur.WeierstrassCoefficientShearResidueCoproductHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueCycleNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeComponents
import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeOver

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
local notation "N" => coefficientShearResidueCycleCoproduct
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "J" => coefficientShearResidueCycleNodes
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "δ" => coefficientShearResidueGluedCoconeOverDesc
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C
local notation "P" => coefficientShearResidueCyclePushoutCocone
  hπ hm data s hs he hstart h3 h4 h6 h6next hc

/-- The full original normalization coproduct factors through the actual Over descent. -/
theorem coefficientShearResidueGluedCoconeOverDesc_components : N ≫ δ = C.inl := by
  apply Sigma.hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (PolygonPinching.componentι Q (2 * s + 4) i).left ≫ (N).left ≫ M = F i
  rw [coefficientShearResidueCycleCoproduct_ι_assoc]
  exact coefficientShearResidueGluedCoconeDesc_component
    hπ hm data s hs he hstart h3 h4 h6 h6next hc C i

/-- Every full original node summand factors through the same actual Over descent. -/
theorem coefficientShearResidueGluedCoconeOverDesc_nodes : J ≫ δ = C.inr := by
  apply Sigma.hom_ext
  intro i
  apply Over.OverMorphism.ext
  change (PolygonPinching.nodeι Q (2 * s + 4) i).left ≫ (J).left ≫ M =
    (PolygonPinching.nodeι Q (2 * s + 4) i ≫ C.inr).left
  rw [coefficientShearResidueCycleNodes_ι_assoc, coefficientShearResidueCycleNode,
    Category.assoc, coefficientShearResidueGluedCoconeDesc_component]
  exact PolygonCyclicPushout.zero_input Q (2 * s + 4) (by omega)
    C.inl C.inr C.condition i

/-- The original component coproduct detects equality of arbitrary morphisms in the slice. -/
theorem coefficientShearResidueCycleOver_hom_ext
    {Y : Over (Spec (.of Q))}
    (f g : Over.mk (coefficientShearGluedStructure hπ data Q r (s + 1) hs) ⟶ Y)
    (h : N ≫ f = N ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  exact coefficientShearResidueCycleCoproduct_hom_ext
    hπ hm data s hs he hstart h3 h4 h6 h6next hc f.left g.left
    (congrArg (fun t => t.left) h)

/-- The actual residue pinching cocone satisfies the full original universal property. -/
def coefficientShearResidueCycleIsColimit : IsColimit P := by
  refine PushoutCocone.IsColimit.mk _
    (fun C => coefficientShearResidueGluedCoconeOverDesc
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C) ?_ ?_ ?_
  · intro C
    exact coefficientShearResidueGluedCoconeOverDesc_components
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C
  · intro C
    exact coefficientShearResidueGluedCoconeOverDesc_nodes
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C
  · intro C f hf _
    apply coefficientShearResidueCycleOver_hom_ext
      hπ hm data s hs he hstart h3 h4 h6 h6next hc f
    exact hf.trans (coefficientShearResidueGluedCoconeOverDesc_components
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C).symm

/-- The given normalization and node maps form the original pushout square over Q. -/
theorem coefficientShearResidueCycle_isPushout :
    IsPushout (PolygonPinching.toComponents Q (2 * s + 4) (by omega))
      (PolygonPinching.toNodes Q (2 * s + 4)) N J :=
  ⟨⟨coefficientShearResidueCycleCoproduct_cocone
    hπ hm data s hs he hstart h3 h4 h6 h6next hc⟩,
    ⟨coefficientShearResidueCycleIsColimit
      hπ hm data s hs he hstart h3 h4 h6 h6next hc⟩⟩

end FLT.Mazur.WeierstrassDividedDepth
