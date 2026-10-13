/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing
public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasStructure
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasStructure

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

local notation "T" => coefficientShearResidueTensorCoconeDesc
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C
local notation "M" => coefficientShearResidueGluedCoconeDesc
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C

/-- The tensor cocone descent preserves the actual coefficient projection. -/
theorem coefficientShearResidueTensorCoconeDesc_structure :
    T ≫ C.pt.hom = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
      (finiteGlobalStructure hπ data (s + 1) hs) := by
  apply (cover).hom_ext
  intro i
  change A i.down ≫ (T ≫ C.pt.hom) = A i.down ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
      (finiteGlobalStructure hπ data (s + 1) hs)
  rw [← Category.assoc, coefficientShearResidueTensorCoconeDesc_chart,
    coefficientShearResidueAtlasCoconeMap_structure]
  exact (coefficientShearAtlasMap_structure hπ data Q r (s + 1) hs i.down).symm

/-- The whole actual equation gluing descends over the coefficient field. -/
theorem coefficientShearResidueGluedCoconeDesc_structure :
    M ≫ C.pt.hom = coefficientShearGluedStructure hπ data Q r (s + 1) hs := by
  rw [coefficientShearResidueGluedCoconeDesc, Category.assoc,
    coefficientShearResidueTensorCoconeDesc_structure]
  rfl

/-- The arbitrary original pinching cocone induces a genuine morphism in Over. -/
def coefficientShearResidueGluedCoconeOverDesc :
    Over.mk (coefficientShearGluedStructure hπ data Q r (s + 1) hs) ⟶ C.pt :=
  Over.homMk M (coefficientShearResidueGluedCoconeDesc_structure
    hπ hm data s hs he hstart h3 h4 h6 h6next hc C)

/-- Full original chart equations uniquely determine the descended morphism in Over. -/
theorem coefficientShearResidueGluedCoconeOverDesc_unique
    (f : Over.mk (coefficientShearGluedStructure hπ data Q r (s + 1) hs) ⟶ C.pt)
    (hf : ∀ i, coefficientShearGluedChart hπ data Q r (s + 1) hs i ≫ f.left = D i) :
    f = coefficientShearResidueGluedCoconeOverDesc
      hπ hm data s hs he hstart h3 h4 h6 h6next hc C := by
  apply Over.OverMorphism.ext
  exact coefficientShearResidueGluedCoconeDesc_unique
    hπ hm data s hs he hstart h3 h4 h6 h6next hc C f.left hf

end FLT.Mazur.WeierstrassDividedDepth
