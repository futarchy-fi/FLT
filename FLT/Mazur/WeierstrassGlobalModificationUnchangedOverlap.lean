/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationUnchangedLift
public import FLT.Mazur.WeierstrassGlobalModificationLocalAction

/-!
# Actual action-cover overlaps with unchanged output

The local action maps agree on their full categorical intersections whenever
either member has original X or Y output. The other member may have affine
output and may have been constructed by a regular-center Rees lift.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
  (i j : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀)

/-- The contractions of the two local actions agree on their entire actual intersection. -/
theorem smoothActionLocal_overlap_contraction :
    pullback.fst (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f i)
        (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f j) ≫
        smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      pullback.snd (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f i)
        (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f j) ≫
        smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs j ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs := by
  rw [smoothActionLocal_contraction, smoothActionLocal_contraction,
    pullback.condition_assoc]

/-- Any competing lift agrees with the local action on an unchanged output member. -/
theorem smoothActionLocal_unique_unchanged
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 ≠ 2)
    {T : Scheme.{u}}
    (p : T ⟶ Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i))
    (f : T ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs) :
    f = p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i := by
  by_cases h0 : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 0
  · have he : smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i =
        smoothXOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i h0 := by
      simp only [smoothActionLocal, dite_eq_left h0]
    rw [he, smoothXOutputToGlobal, ← Category.assoc]
    apply lift_eq_originalX
    rw [hf, he, smoothXOutputToGlobal, Category.assoc,
      originalXChart_contraction, Category.assoc]
  · have h1 : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 1 :=
      by omega
    have he : smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i =
        smoothInfinityOutputToGlobal W s b3 b4 b6 h3 h4 h6 hs i h1 := by
      simp only [smoothActionLocal, dite_eq_right h0, dite_eq_left h1]
    rw [he, smoothInfinityOutputToGlobal, ← Category.assoc]
    apply lift_eq_infinity
    rw [hf, he, smoothInfinityOutputToGlobal, Category.assoc,
      infinityChart_contraction, Category.assoc]

/-- Full actual overlap compatibility when at least one output member is unchanged. -/
theorem smoothActionLocal_overlap_unchanged
    (hij : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 ≠ 2 ∨
      modifiedSmoothOutputIndex W (originalInputContraction W s j.1) j.2 ≠ 2) :
    pullback.fst (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f i)
        (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f j) ≫
        smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i =
      pullback.snd (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f i)
        (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f j) ≫
        smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs j := by
  rcases hij with hi | hj
  · symm
    apply smoothActionLocal_unique_unchanged W s b3 b4 b6 h3 h4 h6 hs i hi
    rw [Category.assoc]
    exact (smoothActionLocal_overlap_contraction W s b3 b4 b6 h3 h4 h6 hs i j).symm
  · apply smoothActionLocal_unique_unchanged W s b3 b4 b6 h3 h4 h6 hs j hj
    rw [Category.assoc]
    exact smoothActionLocal_overlap_contraction W s b3 b4 b6 h3 h4 h6 hs i j

end FLT.Mazur.WeierstrassGlobalModification
