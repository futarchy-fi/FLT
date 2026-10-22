/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankThickenings

/-!
# Universal maps into full independent rank charts

A coefficient map and two compatible maps to the original ideal-power stages
construct a unique map to the double chart. These maps preserve the complete
stages, so they can transport equations before taking radicals or reductions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B Z : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (n m r s : ℕ)

/-- The first full ideal-power rank coordinate. -/
def doubleRankFirst : doubleRankThickening E x y n m r s ⟶ rankThickening E n r :=
  pullback.snd _ _ ≫ pullback.fst _ _

/-- The second full ideal-power rank coordinate. -/
def doubleRankSecond : doubleRankThickening E x y n m r s ⟶ rankThickening E m s :=
  pullback.fst _ _

/-- The first coordinate lies over the unchanged first endpoint. -/
@[reassoc (attr := simp)]
theorem doubleRankFirst_map :
    doubleRankFirst E x y n m r s ≫ rankThickeningMap E n r =
      doubleRankMap E x y n m r s ≫ x := by
  simp only [doubleRankFirst, doubleRankMap, rankPullbackMap, Category.assoc,
    pullback.condition]

/-- The second coordinate lies over the unchanged second endpoint. -/
@[reassoc (attr := simp)]
theorem doubleRankSecond_map :
    doubleRankSecond E x y n m r s ≫ rankThickeningMap E m s =
      doubleRankMap E x y n m r s ≫ y := by
  exact pullback.condition.trans (Category.assoc _ _ _).symm

/-- Construct the full chart map from independent compatible stage coordinates. -/
def doubleRankLift (b : Z ⟶ B) (u : Z ⟶ rankThickening E n r)
    (v : Z ⟶ rankThickening E m s)
    (hu : u ≫ rankThickeningMap E n r = b ≫ x)
    (hv : v ≫ rankThickeningMap E m s = b ≫ y) :
    Z ⟶ doubleRankThickening E x y n m r s :=
  pullback.lift v (pullback.lift u b hu) (by
    simpa only [rankPullbackMap, pullback.lift_snd_assoc] using hv)

variable (b : Z ⟶ B) (u : Z ⟶ rankThickening E n r)
  (v : Z ⟶ rankThickening E m s)
  (hu : u ≫ rankThickeningMap E n r = b ≫ x)
  (hv : v ≫ rankThickeningMap E m s = b ≫ y)

/-- The constructed lift retains the original coefficient map. -/
@[reassoc (attr := simp)]
theorem doubleRankLift_map :
    doubleRankLift E x y n m r s b u v hu hv ≫ doubleRankMap E x y n m r s = b := by
  simp only [doubleRankLift, doubleRankMap, rankPullbackMap, pullback.lift_snd_assoc,
    pullback.lift_snd]

/-- The constructed lift retains the full first rank coordinate. -/
@[reassoc (attr := simp)]
theorem doubleRankLift_first :
    doubleRankLift E x y n m r s b u v hu hv ≫ doubleRankFirst E x y n m r s = u := by
  simp only [doubleRankLift, doubleRankFirst, pullback.lift_snd_assoc, pullback.lift_fst]

/-- The constructed lift retains the full second rank coordinate. -/
@[reassoc (attr := simp)]
theorem doubleRankLift_second :
    doubleRankLift E x y n m r s b u v hu hv ≫ doubleRankSecond E x y n m r s = v := by
  exact pullback.lift_fst _ _ _

/-- Full chart maps are determined by the original coefficient and two rank coordinates. -/
theorem doubleRank_hom_ext (a b : Z ⟶ doubleRankThickening E x y n m r s)
    (h₀ : a ≫ doubleRankMap E x y n m r s = b ≫ doubleRankMap E x y n m r s)
    (h₁ : a ≫ doubleRankFirst E x y n m r s = b ≫ doubleRankFirst E x y n m r s)
    (h₂ : a ≫ doubleRankSecond E x y n m r s = b ≫ doubleRankSecond E x y n m r s) :
    a = b := by
  apply pullback.hom_ext h₂
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans (h₁.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (h₀.trans (Category.assoc _ _ _).symm)

end FLT.Mazur.RelativeOrderedTuples
