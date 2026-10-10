/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalZeroExterior
public import FLT.Mazur.WeierstrassDividedEqualityNodeFamily
public import FLT.Mazur.WeierstrassDividedLaurentTerminalProjectiveComponent

/-!
# The full component endpoints in the equality-depth attachment family

The exterior and adjacent components retain their original sections.
The single complete terminal projective line joins the last retained pair.
All statements use the actual maps over the residue field.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (s + 1) hs)

local notation "N" => equalityNodeOverSection hπ data D s hs hk

/-- Zero of each complete adjacent component is its preceding original attachment. -/
@[reassoc] theorem equalityAdjacentOverComponent_zero (j : Fin s) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫ finalAdjacentOverComponent hπ data D s hs hk j i =
      N (.inr (⟨j.val, by omega⟩, i)) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.zero K ≫ finalAdjacentComponent hπ data D s hs hk j i = _
  rw [finalAdjacentComponent, ← Category.assoc, orderedAdjacentComponent_zero,
    retainedNodeSectionAt_index_transport hπ data D _ _ (by omega)]
  rfl

/-- Infinity of each adjacent component is its next original attachment. -/
@[reassoc] theorem equalityAdjacentOverComponent_infinity (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫ finalAdjacentOverComponent hπ data D s hs hk j i =
      N (.inr (⟨j.val + 1, by omega⟩, i)) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.infinity K ≫ finalAdjacentComponent hπ data D s hs hk j i = _
  rw [finalAdjacentComponent, ← Category.assoc, orderedAdjacentComponent_infinity,
    retainedNodeSectionAt_index_transport hπ data D _ _ (by omega)]
  rfl

/-- The exterior zero endpoint is the original first retained attachment. -/
@[reassoc] theorem equalityZeroExteriorOverComponent_zero (hstart : start = 0) :
    ProjectiveLine.zeroSection K ≫ finalZeroExteriorOverComponent hπ data D s hs hstart hk =
      N (.inr (0, 0)) := by
  apply Over.OverMorphism.ext
  have H := retainedNodeSectionAt_index_transport hπ data D
    (a := 0 + 1 + s) (b := s + 1) (by omega) hs (by omega) 0 (by omega) (by omega) 0
  rw [retainedNodeSectionAt_original hπ data D 0 (by omega) s (by omega),
    orderedRetainedSection_zero hπ data D 0 (by omega) s (by omega) (by omega)
      (by omega)] at H
  change ProjectiveLine.zero K ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  rw [finalZeroExteriorComponent, ← Category.assoc, zeroRetainedOrientedToGlobal_zero]
  exact H

/-- The exterior infinity endpoint is the original second retained attachment. -/
@[reassoc] theorem equalityZeroExteriorOverComponent_infinity (hstart : start = 0) :
    ProjectiveLine.infinitySection K ≫
      finalZeroExteriorOverComponent hπ data D s hs hstart hk = N (.inr (0, 1)) := by
  apply Over.OverMorphism.ext
  have H := retainedNodeSectionAt_index_transport hπ data D
    (a := 0 + 1 + s) (b := s + 1) (by omega) hs (by omega) 0 (by omega) (by omega) 1
  rw [retainedNodeSectionAt_original hπ data D 0 (by omega) s (by omega),
    orderedRetainedSection_zero hπ data D 0 (by omega) s (by omega) (by omega)
      (by omega)] at H
  change ProjectiveLine.infinity K ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  rw [finalZeroExteriorComponent, ← Category.assoc, zeroRetainedOrientedToGlobal_infinity]
  exact H

variable (hp : 2 * (start + s + 1) = depth)

/-- The single complete terminal projective component over the residue field. -/
def equalityTerminalOverComponent : PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (laurentTerminalProjectiveComponent hπ data D s hs hk hp)
    (laurentTerminalProjectiveComponent_structure hπ data D s hs hk hp)

/-- The full terminal zero is the first attachment of the last retained pair. -/
@[reassoc] theorem equalityTerminalOverComponent_zero :
    ProjectiveLine.zeroSection K ≫ equalityTerminalOverComponent hπ data D s hs hk hp =
      N (.inr (⟨s, by omega⟩, 0)) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.zero K ≫ laurentTerminalProjectiveComponent hπ data D s hs hk hp =
    retainedNodeSectionAt hπ data D (s + 1) hs s (by omega) hk 0
  rw [retainedNodeSectionAt_original hπ data D s hs 0 hs hk]
  by_cases h : 0 < start + s
  · rw [orderedRetainedSection_positive hπ data D s hs 0 hs hk h]
    exact laurentTerminalProjectiveComponent_zero_positive hπ data D s hs hk hp h
  · rw [orderedRetainedSection_zero hπ data D s hs 0 hs hk (by omega)]
    exact laurentTerminalProjectiveComponent_zero hπ data D s hs hk hp (by omega)

/-- The full terminal infinity is the other attachment, with no additional terminal node. -/
@[reassoc] theorem equalityTerminalOverComponent_infinity :
    ProjectiveLine.infinitySection K ≫ equalityTerminalOverComponent hπ data D s hs hk hp =
      N (.inr (⟨s, by omega⟩, 1)) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.infinity K ≫
    laurentTerminalProjectiveComponent hπ data D s hs hk hp =
      retainedNodeSectionAt hπ data D (s + 1) hs s (by omega) hk 1
  rw [retainedNodeSectionAt_original hπ data D s hs 0 hs hk]
  by_cases h : 0 < start + s
  · rw [orderedRetainedSection_positive hπ data D s hs 0 hs hk h]
    exact laurentTerminalProjectiveComponent_infinity_positive hπ data D s hs hk hp h
  · rw [orderedRetainedSection_zero hπ data D s hs 0 hs hk (by omega)]
    exact laurentTerminalProjectiveComponent_infinity hπ data D s hs hk hp (by omega)

end FLT.Mazur.WeierstrassDividedDepth
