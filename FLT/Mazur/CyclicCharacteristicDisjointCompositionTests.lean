/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointCompositionComponents

/-!
# Tests of the assembled composition morphism

Arbitrary composable scheme maps lift to the global fiber product. On maps into
specified ordered-pair components, composition recovers the original parameters.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- A pair of actual global arrows with equal middle endpoints. -/
def disjointComposableLift {T : Scheme} (a z : T ⟶ disjointComparisonArrows n)
    (h : a ≫ tgt = z ≫ src) : T ⟶ disjointComposableScheme n :=
  pullback.lift a z h

/-- The global lift retains its first arrow. -/
@[reassoc] theorem disjointComposableLift_first {T : Scheme}
    (a z : T ⟶ disjointComparisonArrows n) (h : a ≫ tgt = z ≫ src) :
    disjointComposableLift n a z h ≫ pullback.fst tgt src = a := pullback.lift_fst _ _ _

/-- The global lift retains its second arrow. -/
@[reassoc] theorem disjointComposableLift_second {T : Scheme}
    (a z : T ⟶ disjointComparisonArrows n) (h : a ≫ tgt = z ≫ src) :
    disjointComposableLift n a z h ≫ pullback.snd tgt src = z := pullback.lift_snd _ _ _

/-- Restricting a global composable lift restricts its two arrows. -/
theorem disjointComposableLift_precomp {T U : Scheme} (f : U ⟶ T)
    (a z : T ⟶ disjointComparisonArrows n) (h : a ≫ tgt = z ≫ src) :
    f ≫ disjointComposableLift n a z h =
      disjointComposableLift n (f ≫ a) (f ≫ z) (by
          simpa only [Category.assoc] using congrArg (fun k ↦ f ≫ k) h) := by
  apply pullback.hom_ext <;> simp only [Category.assoc,
    disjointComposableLift_first, disjointComposableLift_second]

/-- Component parameters factor through the original composable scheme. -/
theorem disjointComposableLift_parameters {T : Scheme} {b c d : Bool}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    {s : T ⟶ normalizedLocus n d} (a : ProductArrow n q r) (z : ProductArrow n r s)
    (h : (a.val ≫ disjointComparisonInclusion n b c) ≫ tgt =
      (z.val ≫ disjointComparisonInclusion n c d) ≫ src) :
    disjointComposableLift n (a.val ≫ disjointComparisonInclusion n b c)
        (z.val ≫ disjointComparisonInclusion n c d) h =
      productComposableLift n b c d a z ≫ disjointComposableInclusion n b c d := by
  apply pullback.hom_ext
  · simp only [disjointComposableLift_first, Category.assoc,
      disjointComposableInclusion_first, productComposableLift_first_assoc]
  · simp only [disjointComposableLift_second, Category.assoc,
      disjointComposableInclusion_second, productComposableLift_second_assoc]

/-- Global composition on component-valued tests is the specified original composition. -/
theorem disjointCompositionMap_apply {T : Scheme} {b c d : Bool}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    {s : T ⟶ normalizedLocus n d} (a : ProductArrow n q r) (z : ProductArrow n r s)
    (h : (a.val ≫ disjointComparisonInclusion n b c) ≫ tgt =
      (z.val ≫ disjointComparisonInclusion n c d) ≫ src) :
    disjointComposableLift n (a.val ≫ disjointComparisonInclusion n b c)
        (z.val ≫ disjointComparisonInclusion n c d) h ≫ disjointCompositionMap n =
      (productArrowComp n a z).val ≫ disjointComparisonInclusion n b d := by
  rw [disjointComposableLift_parameters, Category.assoc,
    disjointCompositionMap_on_parameters]

end FLT.Mazur.CyclicCharacteristicAtlas
