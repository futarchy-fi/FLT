/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroStructure
public import FLT.Mazur.WeierstrassCoefficientShearRetainedZeroStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedZeroStructure
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictZeroRetainedDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictDividedDescent

/-!
# Every original residue atlas cocone map preserves the coefficient field

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

omit [IsBezout R] in
/-- The base equation holds on every entire original atlas chart. -/
theorem coefficientShearResidueStrictZeroAtlasCoconeMap_structure (i : Fin 3 ⊕ Fin (s + 1)) :
    D i ≫ C.pt.hom = coefficientShearAtlasStructure data Q r (s + 1) hs i := by
  have hf (k : Fin (2 * s + 3)) : F k ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 3) k ≫ C.inl).w
  have hrev (k : Fin (2 * s + 3)) :
      (ProjectiveLine.endpointReversal Q ≫ F k) ≫ C.pt.hom = ProjectiveLine.toBase Q := by
    rw [Category.assoc, hf, ProjectiveLine.endpointReversal_toBase]
  rcases i with k | j
  · fin_cases k
    · change D (.inl 0) ≫ C.pt.hom =
        coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 0)
      rw [coefficientShearResidueStrictZeroAtlasCoconeMap_infinity]
      exact coefficientShearResidueStrictZeroInfinityCoconeDesc_structure ..
    · change D (.inl 1) ≫ C.pt.hom =
        coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 1)
      rw [coefficientShearResidueStrictZeroAtlasCoconeMap_divided]
      exact coefficientShearResidueStrictDividedDesc_structure
        hπ hm data s hs hk h3 h4 h6 hc s (2 * s + 3) (by omega) F w C.pt.hom hf
    · change D (.inl 2) ≫ C.pt.hom =
        coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 2)
      rw [coefficientShearResidueStrictZeroAtlasCoconeMap_initial]
      exact coefficientShearResidueStrictZeroInitialCoconeDesc_structure ..
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [coefficientShearResidueStrictZeroAtlasCoconeMap_first,
        coefficientShearResidueStrictZeroFirstCoconeDesc]
      apply coefficientShearRetainedScaleOneZeroDesc_structure
      · exact hrev _
      · exact hf _
      · exact hf _
    · rw [coefficientShearResidueStrictZeroAtlasCoconeMap_positive,
        coefficientShearResidueStrictZeroRetainedDesc]
      apply coefficientShearRetainedZeroDesc_structure
      · exact hrev _
      · exact hf _
      · exact hrev _
      · exact hf _

end FLT.Mazur.WeierstrassDividedDepth
