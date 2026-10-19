/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductOperationSchemes

/-!
# The scheme of composable ordered-pair comparisons

Composition is a scheme morphism on the actual source-target fiber product.
Its value classifies the composite of the two specified compatible arrows.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c d : Bool)
local notation "src" => productArrowSource
local notation "tgt" => productArrowTarget

/-- The actual fiber product parametrizing composable comparisons. -/
def productComposableScheme : Scheme :=
  pullback (tgt n b c) (src n c d)

/-- First comparison in the universal composable pair. -/
def productComposableFirst : productComposableScheme n b c d ⟶ productSubgroupScheme n b c :=
  pullback.fst _ _

/-- Second comparison in the universal composable pair. -/
def productComposableSecond : productComposableScheme n b c d ⟶ productSubgroupScheme n c d :=
  pullback.snd _ _

/-- The middle endpoints coincide by the fiber-product equation. -/
@[reassoc] theorem productComposable_middle :
    productComposableFirst n b c d ≫ tgt n b c =
      productComposableSecond n b c d ≫ src n c d := pullback.condition

/-- First universal arrow with the three composable endpoints retained. -/
def productComposableFirstArrow :
    ProductArrow n (productComposableFirst n b c d ≫ src n b c)
      (productComposableFirst n b c d ≫ tgt n b c) :=
  ⟨productComposableFirst n b c d, by
    apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
        productArrowSource, productArrowTarget]⟩

/-- Second universal arrow uses exactly the same middle endpoint as the first. -/
def productComposableSecondArrow :
    ProductArrow n (productComposableFirst n b c d ≫ tgt n b c)
      (productComposableSecond n b c d ≫ tgt n c d) :=
  ⟨productComposableSecond n b c d, by
    rw [productComposable_middle]
    apply prod.hom_ext <;>
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
        productArrowSource, productArrowTarget]⟩

/-- The actual composition morphism on the scheme of composable comparisons. -/
def productCompositionMap : productComposableScheme n b c d ⟶ productSubgroupScheme n b d :=
  (productArrowComp n (productComposableFirstArrow n b c d)
    (productComposableSecondArrow n b c d)).val

/-- Composition retains the first source. -/
@[reassoc] theorem productCompositionMap_source :
    productCompositionMap n b c d ≫ src n b d =
      productComposableFirst n b c d ≫ src n b c :=
  productArrow_source n b d (productArrowComp n (productComposableFirstArrow n b c d)
    (productComposableSecondArrow n b c d))

/-- Composition retains the second target. -/
@[reassoc] theorem productCompositionMap_target :
    productCompositionMap n b c d ≫ tgt n b d =
      productComposableSecond n b c d ≫ tgt n c d :=
  productArrow_target n b d (productArrowComp n (productComposableFirstArrow n b c d)
    (productComposableSecondArrow n b c d))

/-- Any two actual arrows with a common middle endpoint give a composable scheme test. -/
def productComposableLift {T : Scheme} {q : T ⟶ normalizedLocus n b}
    {r : T ⟶ normalizedLocus n c} {s : T ⟶ normalizedLocus n d}
    (a : ProductArrow n q r) (z : ProductArrow n r s) : T ⟶ productComposableScheme n b c d :=
  pullback.lift a.val z.val ((productArrow_target n b c a).trans
    (productArrow_source n c d z).symm)

/-- The composable test retains the first actual parameter. -/
@[reassoc] theorem productComposableLift_first {T : Scheme}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    {s : T ⟶ normalizedLocus n d} (a : ProductArrow n q r) (z : ProductArrow n r s) :
    productComposableLift n b c d a z ≫ productComposableFirst n b c d = a.val :=
  pullback.lift_fst _ _ _

/-- The composable test retains the second actual parameter. -/
@[reassoc] theorem productComposableLift_second {T : Scheme}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    {s : T ⟶ normalizedLocus n d} (a : ProductArrow n q r) (z : ProductArrow n r s) :
    productComposableLift n b c d a z ≫ productComposableSecond n b c d = z.val :=
  pullback.lift_snd _ _ _

end FLT.Mazur.CyclicCharacteristicAtlas
