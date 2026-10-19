/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointTripleScheme

/-!
# Associativity on triple tests with specified component parameters

A test of the global triple scheme whose three projections are specified
component parameters retains both composites of those exact parameters.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} {b c d e : Bool}
  {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
  {s : T ⟶ normalizedLocus n d} {t : T ⟶ normalizedLocus n e}
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- A triple test retains the actual specified first pair of parameters. -/
theorem disjointTriplePair_parameters (f : T ⟶ disjointTripleScheme n)
    (a : ProductArrow n q r) (z : ProductArrow n r s)
    (ha : f ≫ disjointTripleFirst n = a.val ≫ disjointComparisonInclusion n b c)
    (hz : f ≫ disjointTripleSecond n = z.val ≫ disjointComparisonInclusion n c d) :
    f ≫ disjointTriplePair n =
      productComposableLift n b c d a z ≫ disjointComposableInclusion n b c d := by
  apply pullback.hom_ext
  · simpa only [disjointTripleFirst, Category.assoc, disjointComposableInclusion_first,
      productComposableLift_first_assoc] using ha
  · simpa only [disjointTripleSecond, Category.assoc, disjointComposableInclusion_second,
      productComposableLift_second_assoc] using hz

/-- A triple test retains the actual specified last pair of parameters. -/
theorem disjointTripleLastPair_parameters (f : T ⟶ disjointTripleScheme n)
    (z : ProductArrow n r s) (w : ProductArrow n s t)
    (hz : f ≫ disjointTripleSecond n = z.val ≫ disjointComparisonInclusion n c d)
    (hw : f ≫ disjointTripleThird n = w.val ≫ disjointComparisonInclusion n d e) :
    f ≫ disjointTripleLastPair n =
      productComposableLift n c d e z w ≫ disjointComposableInclusion n c d e := by
  apply pullback.hom_ext
  · simpa only [disjointTripleLastPair, Category.assoc, disjointComposableLift_first,
      disjointComposableInclusion_first, productComposableLift_first_assoc] using hz
  · simpa only [disjointTripleLastPair, Category.assoc, disjointComposableLift_second,
      disjointComposableInclusion_second, productComposableLift_second_assoc] using hw

/-- Left parenthesization retains the composite of the first two specified arrows. -/
theorem disjointTripleLeftInsertion_parameters (f : T ⟶ disjointTripleScheme n)
    (a : ProductArrow n q r) (z : ProductArrow n r s) (w : ProductArrow n s t)
    (ha : f ≫ disjointTripleFirst n = a.val ≫ disjointComparisonInclusion n b c)
    (hz : f ≫ disjointTripleSecond n = z.val ≫ disjointComparisonInclusion n c d)
    (hw : f ≫ disjointTripleThird n = w.val ≫ disjointComparisonInclusion n d e) :
    f ≫ disjointTripleLeftInsertion n =
      productComposableLift n b d e (productArrowComp n a z) w ≫
        disjointComposableInclusion n b d e := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change f ≫ disjointComposableLift n _ _ _ ≫ pullback.fst tgt src = _
    rw [disjointComposableLift_first, ← Category.assoc,
      disjointTriplePair_parameters n f a z ha hz, Category.assoc,
      disjointCompositionMap_on_parameters, Category.assoc,
      disjointComposableInclusion_first, productComposableLift_first_assoc]
  · simpa only [disjointTripleLeftInsertion, Category.assoc, disjointComposableLift_second,
      disjointComposableInclusion_second, productComposableLift_second_assoc] using hw

/-- Right parenthesization retains the composite of the last two specified arrows. -/
theorem disjointTripleRightInsertion_parameters (f : T ⟶ disjointTripleScheme n)
    (a : ProductArrow n q r) (z : ProductArrow n r s) (w : ProductArrow n s t)
    (ha : f ≫ disjointTripleFirst n = a.val ≫ disjointComparisonInclusion n b c)
    (hz : f ≫ disjointTripleSecond n = z.val ≫ disjointComparisonInclusion n c d)
    (hw : f ≫ disjointTripleThird n = w.val ≫ disjointComparisonInclusion n d e) :
    f ≫ disjointTripleRightInsertion n =
      productComposableLift n b c e a (productArrowComp n z w) ≫
        disjointComposableInclusion n b c e := by
  apply pullback.hom_ext
  · simpa only [disjointTripleRightInsertion, Category.assoc, disjointComposableLift_first,
      disjointComposableInclusion_first, productComposableLift_first_assoc] using ha
  · rw [Category.assoc]
    change f ≫ disjointComposableLift n _ _ _ ≫ pullback.snd tgt src = _
    rw [disjointComposableLift_second, ← Category.assoc,
      disjointTripleLastPair_parameters n f z w hz hw, Category.assoc,
      disjointCompositionMap_on_parameters, Category.assoc,
      disjointComposableInclusion_second, productComposableLift_second_assoc]

/-- Both actual global composites agree on every such specified triple test. -/
theorem disjointTriple_associative_parameters (f : T ⟶ disjointTripleScheme n)
    (a : ProductArrow n q r) (z : ProductArrow n r s) (w : ProductArrow n s t)
    (ha : f ≫ disjointTripleFirst n = a.val ≫ disjointComparisonInclusion n b c)
    (hz : f ≫ disjointTripleSecond n = z.val ≫ disjointComparisonInclusion n c d)
    (hw : f ≫ disjointTripleThird n = w.val ≫ disjointComparisonInclusion n d e) :
    f ≫ disjointTripleLeftInsertion n ≫ disjointCompositionMap n =
      f ≫ disjointTripleRightInsertion n ≫ disjointCompositionMap n := by
  rw [← Category.assoc, disjointTripleLeftInsertion_parameters n f a z w ha hz hw,
    Category.assoc, disjointCompositionMap_on_parameters, ← Category.assoc,
    disjointTripleRightInsertion_parameters n f a z w ha hz hw, Category.assoc,
    disjointCompositionMap_on_parameters, productArrowComp_assoc]

end FLT.Mazur.CyclicCharacteristicAtlas
