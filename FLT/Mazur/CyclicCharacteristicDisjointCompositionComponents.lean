/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointComposition

/-!
# Global composition on the original ordered-pair fiber products

The inclusion of each ordered-pair composable scheme into the global fiber
product retains both arrows, and global composition is the original one.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c d : Bool)
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n
local notation "X" => (fun p : Bool × Bool ↦ productSubgroupScheme n (Prod.fst p) (Prod.snd p))
local notation "j" => SchemeCoproductPullback.chartMap X X tgt src

/-- The ordered-pair composable scheme maps into its matching global chart. -/
def productComposableToDisjointChart :
    productComposableScheme n b c d ⟶ disjointComposableChart n ((b, c), (c, d)) :=
  pullback.lift (productComposableFirst n b c d) (productComposableSecond n b c d) (by
    change _ ≫ (disjointComparisonInclusion n b c ≫ tgt) =
      _ ≫ (disjointComparisonInclusion n c d ≫ src)
    rw [disjointComparisonInclusion_target, disjointComparisonInclusion_source,
      productComposable_middle_assoc])

/-- The chart lift retains the first projection. -/
@[reassoc] theorem productComposableToDisjointChart_first :
    productComposableToDisjointChart n b c d ≫ pullback.fst _ _ =
      productComposableFirst n b c d := pullback.lift_fst _ _ _

/-- The chart lift retains the second projection. -/
@[reassoc] theorem productComposableToDisjointChart_second :
    productComposableToDisjointChart n b c d ≫ pullback.snd _ _ =
      productComposableSecond n b c d := pullback.lift_snd _ _ _

/-- Recovering the ordered-pair composable scheme after this chart inclusion is identity. -/
theorem productComposableToDisjointChart_recover :
    productComposableToDisjointChart n b c d ≫ disjointComposableChartToProduct n b c d =
      𝟙 _ := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ productComposableFirst n b c d = _
    rw [Category.assoc, disjointComposableChartToProduct_first, Category.id_comp]
    exact pullback.lift_fst _ _ _
  · change (_ ≫ _) ≫ productComposableSecond n b c d = _
    rw [Category.assoc, disjointComposableChartToProduct_second, Category.id_comp]
    exact pullback.lift_snd _ _ _

/-- The actual inclusion of an original composable pair into the global fiber product. -/
def disjointComposableInclusion :
    productComposableScheme n b c d ⟶ disjointComposableScheme n :=
  productComposableToDisjointChart n b c d ≫ j ((b, c), (c, d))

/-- The component inclusion retains the first original arrow. -/
@[reassoc] theorem disjointComposableInclusion_first :
    disjointComposableInclusion n b c d ≫ pullback.fst tgt src =
      productComposableFirst n b c d ≫ disjointComparisonInclusion n b c := by
  rw [disjointComposableInclusion, Category.assoc, SchemeCoproductPullback.chartMap_fst]
  change _ ≫ _ ≫ disjointComparisonInclusion n b c = _
  exact productComposableToDisjointChart_first_assoc n b c d _

/-- The component inclusion retains the second original arrow. -/
@[reassoc] theorem disjointComposableInclusion_second :
    disjointComposableInclusion n b c d ≫ pullback.snd tgt src =
      productComposableSecond n b c d ≫ disjointComparisonInclusion n c d := by
  rw [disjointComposableInclusion, Category.assoc, SchemeCoproductPullback.chartMap_snd]
  change _ ≫ _ ≫ disjointComparisonInclusion n c d = _
  exact productComposableToDisjointChart_second_assoc n b c d _

/-- Global composition restricts to the actual original ordered-pair composition map. -/
@[reassoc] theorem disjointComposableInclusion_composition :
    disjointComposableInclusion n b c d ≫ disjointCompositionMap n =
      productCompositionMap n b c d ≫ disjointComparisonInclusion n b d := by
  rw [disjointComposableInclusion, Category.assoc, disjointCompositionMap_chart,
    disjointCompositionOnChart_matching, ← Category.assoc,
    productComposableToDisjointChart_recover, Category.id_comp]

/-- Global composition recovers the composite parameter for every specified pair of arrows. -/
theorem disjointCompositionMap_on_parameters {T : Scheme}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    {s : T ⟶ normalizedLocus n d} (a : ProductArrow n q r) (z : ProductArrow n r s) :
    productComposableLift n b c d a z ≫ disjointComposableInclusion n b c d ≫
        disjointCompositionMap n =
      (productArrowComp n a z).val ≫ disjointComparisonInclusion n b d := by
  rw [disjointComposableInclusion_composition, ← Category.assoc, productCompositionMap_apply]

end FLT.Mazur.CyclicCharacteristicAtlas
