/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointTripleScheme

/-!
# Component charts of the triple comparison scheme

The actual triple fiber product is covered by triples of component arrows.
Both middle endpoint equations are inherited from its two fiber products.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n
local notation "X" => (fun p : Bool × Bool ↦ productSubgroupScheme n (Prod.fst p) (Prod.snd p))
local notation "chartInclusion" => SchemeCoproductPullback.chartMap X X tgt src

/-- Component triples form an open cover of the actual iterated fiber product. -/
def disjointTripleCover : (disjointTripleScheme n).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (SchemeCoproductPullback.cover X X tgt src)
    (sigmaOpenCover X) (pullback.snd tgt src ≫ tgt) src

/-- A chart specifies all three ordered-pair labels. -/
abbrev disjointTripleChart (p q r : Bool × Bool) : Scheme :=
  pullback (chartInclusion (p, q) ≫ pullback.snd tgt src ≫ tgt)
    (disjointComparisonInclusion n r.1 r.2 ≫ src)

/-- The chart inclusion retains its two nested fiber products. -/
def disjointTripleChartMap (p q r : Bool × Bool) :
    disjointTripleChart n p q r ⟶ disjointTripleScheme n :=
  (disjointTripleCover n).f ((p, q), r)

/-- First component arrow on a triple chart. -/
def disjointTripleChartFirst (p q r : Bool × Bool) :
    disjointTripleChart n p q r ⟶ productSubgroupScheme n p.1 p.2 :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- Second component arrow on a triple chart. -/
def disjointTripleChartSecond (p q r : Bool × Bool) :
    disjointTripleChart n p q r ⟶ productSubgroupScheme n q.1 q.2 :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- Third component arrow on a triple chart. -/
def disjointTripleChartThird (p q r : Bool × Bool) :
    disjointTripleChart n p q r ⟶ productSubgroupScheme n r.1 r.2 :=
  pullback.snd _ _

/-- The chart inclusion retains the first composable pair. -/
@[reassoc] theorem disjointTripleChartMap_pair (p q r : Bool × Bool) :
    disjointTripleChartMap n p q r ≫ disjointTriplePair n =
      pullback.fst _ _ ≫ chartInclusion (p, q) := pullback.lift_fst _ _ _

/-- The chart inclusion retains the first comparison. -/
@[reassoc] theorem disjointTripleChartMap_first (p q r : Bool × Bool) :
    disjointTripleChartMap n p q r ≫ disjointTripleFirst n =
      disjointTripleChartFirst n p q r ≫ disjointComparisonInclusion n p.1 p.2 := by
  rw [disjointTripleFirst, disjointTripleChartMap_pair_assoc,
    SchemeCoproductPullback.chartMap_fst, ← Category.assoc]
  rfl

/-- The chart inclusion retains the second comparison. -/
@[reassoc] theorem disjointTripleChartMap_second (p q r : Bool × Bool) :
    disjointTripleChartMap n p q r ≫ disjointTripleSecond n =
      disjointTripleChartSecond n p q r ≫ disjointComparisonInclusion n q.1 q.2 := by
  rw [disjointTripleSecond, disjointTripleChartMap_pair_assoc,
    SchemeCoproductPullback.chartMap_snd, ← Category.assoc]
  rfl

/-- The chart inclusion retains the third comparison. -/
@[reassoc] theorem disjointTripleChartMap_third (p q r : Bool × Bool) :
    disjointTripleChartMap n p q r ≫ disjointTripleThird n =
      disjointTripleChartThird n p q r ≫ disjointComparisonInclusion n r.1 r.2 :=
  pullback.lift_snd _ _ _

/-- The first middle endpoints agree after inclusion in the global base. -/
theorem disjointTripleChart_first_middle (p q r : Bool × Bool) :
    disjointTripleChartFirst n p q r ≫ productArrowTarget n p.1 p.2 ≫
        normalizedDisjointInclusion n p.2 =
      disjointTripleChartSecond n p q r ≫ productArrowSource n q.1 q.2 ≫
        normalizedDisjointInclusion n q.1 := by
  have h' := congrArg (disjointTripleChartMap n p q r ≫ ·)
    (disjointTriple_first_middle n)
  simpa only [disjointTripleChartMap_first_assoc, disjointTripleChartMap_second_assoc,
    disjointComparisonInclusion_source,
    disjointComparisonInclusion_target] using h'

/-- The second middle endpoints agree after inclusion in the global base. -/
theorem disjointTripleChart_second_middle (p q r : Bool × Bool) :
    disjointTripleChartSecond n p q r ≫ productArrowTarget n q.1 q.2 ≫
        normalizedDisjointInclusion n q.2 =
      disjointTripleChartThird n p q r ≫ productArrowSource n r.1 r.2 ≫
        normalizedDisjointInclusion n r.1 := by
  have h := congrArg (disjointTripleChartMap n p q r ≫ ·)
    (disjointTriple_second_middle n)
  simpa only [disjointTripleChartMap_second_assoc, disjointTripleChartMap_third_assoc,
    disjointComparisonInclusion_source,
    disjointComparisonInclusion_target] using h

/-- A mismatch at the first middle label gives an empty triple chart. -/
theorem disjointTripleChart_empty_first (p q r : Bool × Bool) (h : p.2 ≠ q.1) :
    IsEmpty (disjointTripleChart n p q r) := by
  apply isEmpty_of_commSq_sigmaι_of_ne (g := normalizedLocus n) (i := p.2) (j := q.1)
    (a := disjointTripleChartFirst n p q r ≫ productArrowTarget n p.1 p.2)
    (b := disjointTripleChartSecond n p q r ≫ productArrowSource n q.1 q.2) _ h
  exact ⟨by simpa only [Category.assoc] using! disjointTripleChart_first_middle n p q r⟩

/-- A mismatch at the second middle label gives an empty triple chart. -/
theorem disjointTripleChart_empty_second (p q r : Bool × Bool) (h : q.2 ≠ r.1) :
    IsEmpty (disjointTripleChart n p q r) := by
  apply isEmpty_of_commSq_sigmaι_of_ne (g := normalizedLocus n) (i := q.2) (j := r.1)
    (a := disjointTripleChartSecond n p q r ≫ productArrowTarget n q.1 q.2)
    (b := disjointTripleChartThird n p q r ≫ productArrowSource n r.1 r.2) _ h
  exact ⟨by simpa only [Category.assoc] using! disjointTripleChart_second_middle n p q r⟩

end FLT.Mazur.CyclicCharacteristicAtlas
