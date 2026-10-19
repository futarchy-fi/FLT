/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointAssociativity
public import FLT.Mazur.CyclicCharacteristicDisjointTestArrows

/-!
# Associativity on arbitrary global scheme tests

Every composable triple of specified global arrows maps to the actual triple
fiber product. Pulling back the global diagram proves its associativity law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  {q r s t : T ⟶ normalizedDisjointSource n}
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- Every specified composable triple maps to the actual triple fiber product. -/
def disjointArrowTripleLift (a : DisjointArrow n q r) (z : DisjointArrow n r s)
    (w : DisjointArrow n s t) : T ⟶ disjointTripleScheme n :=
  pullback.lift (disjointComposableLift n a.val z.val (a.property.2.trans z.property.1.symm))
    w.val (by
      rw [disjointComposableLift_second_assoc]
      exact z.property.2.trans w.property.1.symm)

/-- The triple lift retains its actual first composable pair. -/
@[reassoc] theorem disjointArrowTripleLift_pair (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowTripleLift n a z w ≫ disjointTriplePair n =
      disjointComposableLift n a.val z.val (a.property.2.trans z.property.1.symm) :=
  pullback.lift_fst _ _ _

/-- The triple lift retains the first specified arrow. -/
@[reassoc] theorem disjointArrowTripleLift_first (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowTripleLift n a z w ≫ disjointTripleFirst n = a.val := by
  rw [disjointTripleFirst, disjointArrowTripleLift_pair_assoc, disjointComposableLift_first]

/-- The triple lift retains the second specified arrow. -/
@[reassoc] theorem disjointArrowTripleLift_second (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowTripleLift n a z w ≫ disjointTripleSecond n = z.val := by
  rw [disjointTripleSecond, disjointArrowTripleLift_pair_assoc, disjointComposableLift_second]

/-- The triple lift retains the third specified arrow. -/
@[reassoc] theorem disjointArrowTripleLift_third (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowTripleLift n a z w ≫ disjointTripleThird n = w.val := pullback.lift_snd _ _ _

/-- The triple lift also retains the specified last pair. -/
theorem disjointArrowTripleLift_lastPair (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowTripleLift n a z w ≫ disjointTripleLastPair n =
      disjointComposableLift n z.val w.val (z.property.2.trans w.property.1.symm) := by
  apply pullback.hom_ext <;>
    simp only [disjointTripleLastPair, Category.assoc, disjointComposableLift_first,
      disjointComposableLift_second, disjointArrowTripleLift_second,
      disjointArrowTripleLift_third]

/-- The left insertion induces the left parenthesization of actual global arrows. -/
theorem disjointArrowTripleLift_left (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowTripleLift n a z w ≫ disjointTripleLeftInsertion n =
      disjointComposableLift n (disjointArrowComp n a z).val w.val
        ((disjointArrowComp n a z).property.2.trans w.property.1.symm) := by
  apply pullback.hom_ext
  · simp only [disjointTripleLeftInsertion, Category.assoc, disjointComposableLift_first,
      disjointArrowTripleLift_pair_assoc]
    rfl
  · simp only [disjointTripleLeftInsertion, Category.assoc, disjointComposableLift_second,
      disjointArrowTripleLift_third]

/-- The right insertion induces the right parenthesization of actual global arrows. -/
theorem disjointArrowTripleLift_right (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowTripleLift n a z w ≫ disjointTripleRightInsertion n =
      disjointComposableLift n a.val (disjointArrowComp n z w).val
        (a.property.2.trans (disjointArrowComp n z w).property.1.symm) := by
  apply pullback.hom_ext
  · simp only [disjointTripleRightInsertion, Category.assoc, disjointComposableLift_first,
      disjointArrowTripleLift_first]
  · simp only [disjointTripleRightInsertion, Category.assoc, disjointComposableLift_second]
    rw [← Category.assoc, disjointArrowTripleLift_lastPair]
    rfl

/-- The scheme associativity diagram gives associativity for every specified global triple. -/
theorem disjointArrowComp_assoc (a : DisjointArrow n q r)
    (z : DisjointArrow n r s) (w : DisjointArrow n s t) :
    disjointArrowComp n (disjointArrowComp n a z) w =
      disjointArrowComp n a (disjointArrowComp n z w) := by
  apply Subtype.ext
  have h := congrArg (disjointArrowTripleLift n a z w ≫ ·)
    (disjointCompositionMap_associative n)
  rw [← Category.assoc, disjointArrowTripleLift_left, ← Category.assoc,
    disjointArrowTripleLift_right] at h
  exact h

end FLT.Mazur.CyclicCharacteristicAtlas
