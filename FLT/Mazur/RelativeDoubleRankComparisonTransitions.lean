/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankTransitions
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Cartesian transitions of full rank comparisons

Pulling a fixed comparison to the independent rank stages gives actual
transition maps. The transition squares are cartesian. Whenever the higher
comparison is closed, its entire equation ideal pulls back to the lower one.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B Z : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (n m : ℕ) (c : Z ⟶ B)

/-- Retain the original comparison coordinate while increasing both full rank orders. -/
def doubleRankComparisonTransition {r s r' s' : ℕ} (hr : r ≤ r') (hs : s ≤ s') :
    pullback c (doubleRankMap E x y n m r s) ⟶
      pullback c (doubleRankMap E x y n m r' s') :=
  pullback.lift (pullback.fst c (doubleRankMap E x y n m r s))
    (pullback.snd c (doubleRankMap E x y n m r s) ≫ doubleRankTransition E x y n m hr hs)
    (by rw [Category.assoc, doubleRankTransition_map]; exact pullback.condition)

/-- The map retains the full original comparison source. -/
@[reassoc (attr := simp)]
theorem doubleRankComparisonTransition_first {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankComparisonTransition E x y n m c hr hs ≫
      pullback.fst c (doubleRankMap E x y n m r' s') =
        pullback.fst c (doubleRankMap E x y n m r s) :=
  pullback.lift_fst _ _ _

/-- The coefficient coordinate follows the constructed full order transition. -/
@[reassoc (attr := simp)]
theorem doubleRankComparisonTransition_second {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankComparisonTransition E x y n m c hr hs ≫
      pullback.snd c (doubleRankMap E x y n m r' s') =
        pullback.snd c (doubleRankMap E x y n m r s) ≫
          doubleRankTransition E x y n m hr hs :=
  pullback.lift_snd _ _ _

/-- The entire lower comparison is the base change of the higher comparison. -/
theorem doubleRankComparisonTransition_isPullback {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    IsPullback (pullback.snd c (doubleRankMap E x y n m r s))
      (doubleRankComparisonTransition E x y n m c hr hs)
      (doubleRankTransition E x y n m hr hs)
      (pullback.snd c (doubleRankMap E x y n m r' s')) := by
  apply IsPullback.of_bot (v₂₁ := pullback.fst c (doubleRankMap E x y n m r' s'))
    (v₂₂ := doubleRankMap E x y n m r' s') (h₃₁ := c)
  · rw [doubleRankComparisonTransition_first, doubleRankTransition_map]
    exact (IsPullback.of_hasPullback c (doubleRankMap E x y n m r s)).flip
  · exact (doubleRankComparisonTransition_second E x y n m c hr hs).symm
  · exact (IsPullback.of_hasPullback c (doubleRankMap E x y n m r' s')).flip

/-- The exact ideal of a closed full comparison commutes with both independent order changes. -/
theorem doubleRankComparisonTransition_kernel {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s')
    [IsClosedImmersion (pullback.snd c (doubleRankMap E x y n m r' s'))] :
    (pullback.snd c (doubleRankMap E x y n m r' s')).ker.comap
      (doubleRankTransition E x y n m hr hs) =
        (pullback.snd c (doubleRankMap E x y n m r s)).ker := by
  let H := doubleRankComparisonTransition_isPullback E x y n m c hr hs
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

end FLT.Mazur.RelativeOrderedTuples
