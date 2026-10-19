/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointCompositionTests

/-!
# The scheme of three composable global comparisons

Both parenthesizations are morphisms out of the same actual iterated fiber
product. Its projections retain all three specified comparison arrows.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- The actual iterated fiber product of three composable arrows. -/
def disjointTripleScheme : Scheme := pullback (pullback.snd tgt src ≫ tgt) src

/-- The first two arrows as a point of the composable scheme. -/
def disjointTriplePair : disjointTripleScheme n ⟶ disjointComposableScheme n :=
  pullback.fst _ _

/-- First arrow of the universal composable triple. -/
def disjointTripleFirst : disjointTripleScheme n ⟶ disjointComparisonArrows n :=
  disjointTriplePair n ≫ pullback.fst tgt src

/-- Second arrow of the universal composable triple. -/
def disjointTripleSecond : disjointTripleScheme n ⟶ disjointComparisonArrows n :=
  disjointTriplePair n ≫ pullback.snd tgt src

/-- Third arrow of the universal composable triple. -/
def disjointTripleThird : disjointTripleScheme n ⟶ disjointComparisonArrows n :=
  pullback.snd _ _

/-- The first two arrows have the same middle endpoint. -/
@[reassoc] theorem disjointTriple_first_middle :
    disjointTripleFirst n ≫ tgt = disjointTripleSecond n ≫ src := by
  simp only [disjointTripleFirst, disjointTripleSecond, Category.assoc, pullback.condition]

/-- The last two arrows have the same middle endpoint. -/
@[reassoc] theorem disjointTriple_second_middle :
    disjointTripleSecond n ≫ tgt = disjointTripleThird n ≫ src := by
  simpa only [disjointTripleSecond, disjointTriplePair, disjointTripleThird,
    Category.assoc] using (pullback.condition (f := pullback.snd tgt src ≫ tgt) (g := src))

/-- The last two arrows as a point of the composable scheme. -/
def disjointTripleLastPair : disjointTripleScheme n ⟶ disjointComposableScheme n :=
  disjointComposableLift n (disjointTripleSecond n) (disjointTripleThird n)
    (disjointTriple_second_middle n)

/-- Compose the first two arrows, retaining the third. -/
def disjointTripleLeftInsertion : disjointTripleScheme n ⟶ disjointComposableScheme n :=
  disjointComposableLift n (disjointTriplePair n ≫ disjointCompositionMap n)
    (disjointTripleThird n) (by
      rw [Category.assoc, disjointCompositionMap_target]
      exact pullback.condition)

/-- Retain the first arrow and compose the last two. -/
def disjointTripleRightInsertion : disjointTripleScheme n ⟶ disjointComposableScheme n :=
  disjointComposableLift n (disjointTripleFirst n)
    (disjointTripleLastPair n ≫ disjointCompositionMap n) (by
      rw [Category.assoc, disjointCompositionMap_source, ← Category.assoc]
      change _ = (disjointComposableLift n _ _ _ ≫ pullback.fst tgt src) ≫ src
      rw [disjointComposableLift_first]
      exact disjointTriple_first_middle n)

/-- The first pair can be recovered directly from its two arrow projections. -/
theorem disjointTriplePair_eq_lift :
    disjointTriplePair n = disjointComposableLift n (disjointTripleFirst n)
      (disjointTripleSecond n) (disjointTriple_first_middle n) := by
  apply pullback.hom_ext <;>
    simp only [disjointComposableLift_first, disjointComposableLift_second]
  <;> rfl

end FLT.Mazur.CyclicCharacteristicAtlas
