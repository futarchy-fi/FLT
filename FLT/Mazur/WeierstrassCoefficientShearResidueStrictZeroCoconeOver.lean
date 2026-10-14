/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasStructure
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasStructure

/-!
# The complete original cocone descends over its coefficient base

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
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)
    (Nat.zero_lt_succ (2 * s + 2)))
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

local notation "T" => coefficientShearResidueStrictZeroTensorCoconeDesc
  hπ hm data s hs hk h3 h4 h6 hc C
local notation "M" => coefficientShearResidueStrictZeroGluedCoconeDesc
  hπ hm data s hs hk h3 h4 h6 hc C

/-- The tensor cocone descent preserves the actual coefficient projection. -/
theorem coefficientShearResidueStrictZeroTensorCoconeDesc_structure :
    T ≫ C.pt.hom = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
      (finiteGlobalStructure hπ data (s + 1) hs) := by
  apply (cover).hom_ext
  intro i
  change A i.down ≫ (T ≫ C.pt.hom) = A i.down ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
      (finiteGlobalStructure hπ data (s + 1) hs)
  rw [← Category.assoc, coefficientShearResidueStrictZeroTensorCoconeDesc_chart,
    coefficientShearResidueStrictZeroAtlasCoconeMap_structure]
  exact (coefficientShearAtlasMap_structure hπ data Q r (s + 1) hs i.down).symm

/-- The whole actual equation gluing descends over the coefficient field. -/
theorem coefficientShearResidueStrictZeroGluedCoconeDesc_structure :
    M ≫ C.pt.hom = coefficientShearGluedStructure hπ data Q r (s + 1) hs := by
  rw [coefficientShearResidueStrictZeroGluedCoconeDesc, Category.assoc,
    coefficientShearResidueStrictZeroTensorCoconeDesc_structure]
  rfl

/-- The arbitrary original pinching cocone induces a genuine morphism in Over. -/
def coefficientShearResidueStrictZeroGluedCoconeOverDesc :
    Over.mk (coefficientShearGluedStructure hπ data Q r (s + 1) hs) ⟶ C.pt :=
  Over.homMk M (coefficientShearResidueStrictZeroGluedCoconeDesc_structure
    hπ hm data s hs hk h3 h4 h6 hc C)

/-- Full original chart equations uniquely determine the descended morphism in Over. -/
theorem coefficientShearResidueStrictZeroGluedCoconeOverDesc_unique
    (f : Over.mk (coefficientShearGluedStructure hπ data Q r (s + 1) hs) ⟶ C.pt)
    (hf : ∀ i, coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫ f.left = D i) :
    f = coefficientShearResidueStrictZeroGluedCoconeOverDesc
      hπ hm data s hs hk h3 h4 h6 hc C := by
  apply Over.OverMorphism.ext
  exact coefficientShearResidueStrictZeroGluedCoconeDesc_unique
    hπ hm data s hs hk h3 h4 h6 hc C f.left hf

end FLT.Mazur.WeierstrassDividedDepth
