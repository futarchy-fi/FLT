/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeRestrictions
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeOver
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoproductHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroCycleNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeRestrictions
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeOver

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
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueZeroGluedCoconeDesc
  hπ hm data s hs he h3 h4 h6next hc C
local notation "N" => coefficientShearResidueZeroEqualityCycleCoproduct
  hπ hm data s hs he h3 h4 h6next hc
local notation "J" => coefficientShearResidueZeroEqualityCycleNodes
  hπ hm data s hs he h3 h4 h6next hc
local notation "δ" => coefficientShearResidueZeroGluedCoconeOverDesc
  hπ hm data s hs he h3 h4 h6next hc C
local notation "P" => coefficientShearResidueZeroEqualityCyclePushoutCocone
  hπ hm data s hs he h3 h4 h6next hc

/-- The original component coproduct detects equality of arbitrary morphisms in the slice. -/
theorem coefficientShearResidueZeroEqualityCycleOver_hom_ext
    {Y : Over (Spec (.of Q))}
    (f g : Over.mk (coefficientShearGluedStructure hπ data Q r (s + 1) hs) ⟶ Y)
    (h : N ≫ f = N ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  exact coefficientShearResidueZeroEqualityCycleCoproduct_hom_ext
    hπ hm data s hs he h3 h4 h6next hc f.left g.left
    (congrArg (fun t => t.left) h)

/-- The actual residue pinching cocone satisfies the full original universal property. -/
def coefficientShearResidueZeroEqualityCycleIsColimit : IsColimit P := by
  refine PushoutCocone.IsColimit.mk _
    (fun C => coefficientShearResidueZeroGluedCoconeOverDesc
      hπ hm data s hs he h3 h4 h6next hc C) ?_ ?_ ?_
  · intro C
    exact coefficientShearResidueZeroGluedCoconeOverDesc_components
      hπ hm data s hs he h3 h4 h6next hc C
  · intro C
    exact coefficientShearResidueZeroGluedCoconeOverDesc_nodes
      hπ hm data s hs he h3 h4 h6next hc C
  · intro C f hf _
    apply coefficientShearResidueZeroEqualityCycleOver_hom_ext
      hπ hm data s hs he h3 h4 h6next hc f
    exact hf.trans (coefficientShearResidueZeroGluedCoconeOverDesc_components
      hπ hm data s hs he h3 h4 h6next hc C).symm

/-- The given normalization and node maps form the original pushout square over Q. -/
theorem coefficientShearResidueZeroEqualityCycle_isPushout :
    IsPushout (PolygonPinching.toComponents Q (2 * s + 2) (by omega))
      (PolygonPinching.toNodes Q (2 * s + 2)) N J :=
  ⟨⟨coefficientShearResidueZeroEqualityCycleCoproduct_cocone
    hπ hm data s hs he h3 h4 h6next hc⟩,
    ⟨coefficientShearResidueZeroEqualityCycleIsColimit
      hπ hm data s hs he h3 h4 h6next hc⟩⟩

end FLT.Mazur.WeierstrassDividedDepth
