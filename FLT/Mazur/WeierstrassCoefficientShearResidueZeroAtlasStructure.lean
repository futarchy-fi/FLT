/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneZeroStructure
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneEqualityStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneEqualityStructure
public import FLT.Mazur.WeierstrassCoefficientShearRetainedZeroStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedZeroStructure
public import FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityStructure
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent

/-!
# All original start-zero atlas cocone maps preserve the base

The first retained equation uses its original scale-one conic, including at length two.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
  (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C

/-- Every complete original atlas map retains its coefficient field structure. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_structure (i : Fin 3 ⊕ Fin (s + 1)) :
    D i ≫ C.pt.hom = coefficientShearAtlasStructure data Q r (s + 1) hs i := by
  have hf (k : Fin (2 * s + 2)) : F k ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 2) k ≫ C.inl).w
  have hrev (k : Fin (2 * s + 2)) :
      (ProjectiveLine.endpointReversal Q ≫ F k) ≫ C.pt.hom = ProjectiveLine.toBase Q := by
    rw [Category.assoc, hf, ProjectiveLine.endpointReversal_toBase]
  rcases i with k | j
  · fin_cases k
    · change D (.inl 0) ≫ C.pt.hom =
        coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 0)
      rw [coefficientShearResidueZeroAtlasCoconeMap_infinity]
      exact coefficientShearResidueZeroInfinityCoconeDesc_structure ..
    · change D (.inl 1) ≫ C.pt.hom =
        coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 1)
      rw [coefficientShearResidueZeroAtlasCoconeMap_divided,
        coefficientShearResidueZeroDividedCoconeDesc, coefficientShearResidueZeroDividedDesc]
      simp only [Category.assoc]
      rw [hf, ProjectiveLine.endpointReversal_toBase,
        coefficientShearEqualityDividedParameter_structure]
    · change D (.inl 2) ≫ C.pt.hom =
        coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 2)
      rw [coefficientShearResidueZeroAtlasCoconeMap_initial]
      exact coefficientShearResidueZeroInitialCoconeDesc_structure ..
  · rw [coefficientShearResidueZeroAtlasCoconeMap_retained]
    by_cases h0 : j.val = 0
    · have hj : j = ⟨0, Nat.zero_lt_succ s⟩ := Fin.ext h0
      subst j
      by_cases hs0 : s = 0
      · subst s
        rw [coefficientShearResidueZeroRetainedCoconeMap]
        simp only [↓reduceDIte]
        rw [coefficientShearResidueZeroLengthTwoCoconeDesc]
        apply coefficientShearRetainedScaleOneEqualityDesc_structure
        · exact hrev _
        · exact hf _
      · rw [coefficientShearResidueZeroRetainedCoconeMap_first
          hπ hm data s hs he h3 h4 h6next hc C (Nat.pos_of_ne_zero hs0),
          coefficientShearResidueZeroFirstCoconeDesc]
        apply coefficientShearRetainedScaleOneZeroDesc_structure
        · exact hrev _
        · exact hf _
        · exact hf _
    · by_cases hlast : j.val = s
      · have hj : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext hlast
        subst j
        rw [coefficientShearResidueZeroRetainedCoconeMap_last
          hπ hm data s hs he h3 h4 h6next hc C (Nat.pos_of_ne_zero h0),
          coefficientShearResidueZeroLastDesc]
        apply coefficientShearRetainedEqualityDesc_structure
        · exact hrev _
        · exact hrev _
        · exact hf _
      · let k : Fin s := ⟨j.val, by omega⟩
        have hj : j = k.castSucc := Fin.ext rfl
        rw [hj, coefficientShearResidueZeroRetainedCoconeMap_interior
          hπ hm data s hs he h3 h4 h6next hc C k (Nat.pos_of_ne_zero h0),
          coefficientShearResidueZeroInteriorDesc]
        apply coefficientShearRetainedZeroDesc_structure
        · exact hrev _
        · exact hf _
        · exact hrev _
        · exact hf _

/-- Each full original chart map is a morphism over the same coefficient field. -/
def coefficientShearResidueZeroAtlasCoconeOverMap (i : Fin 3 ⊕ Fin (s + 1)) :
    Over.mk (coefficientShearAtlasStructure data Q r (s + 1) hs i) ⟶ C.pt :=
  Over.homMk (D i) (coefficientShearResidueZeroAtlasCoconeMap_structure
    hπ hm data s hs he h3 h4 h6next hc C i)

end FLT.Mazur.WeierstrassDividedDepth
