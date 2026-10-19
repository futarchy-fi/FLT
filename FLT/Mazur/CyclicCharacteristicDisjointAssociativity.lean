/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointTripleCharts
public import FLT.Mazur.CyclicCharacteristicDisjointTripleParameterTests

/-!
# Global associativity of the normalized comparison atlas

On matching charts the original three parameters prove associativity. Every
other chart is empty. The open cover then gives the actual global diagram.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Matching triple charts retain three composable parameters and their associativity. -/
theorem disjointTripleChart_associative (b c d e : Bool) :
    disjointTripleChartMap n (b, c) (c, d) (d, e) ≫
        disjointTripleLeftInsertion n ≫ disjointCompositionMap n =
      disjointTripleChartMap n (b, c) (c, d) (d, e) ≫
        disjointTripleRightInsertion n ≫ disjointCompositionMap n := by
  let f₁ := disjointTripleChartFirst n (b, c) (c, d) (d, e)
  let f₂ := disjointTripleChartSecond n (b, c) (c, d) (d, e)
  let f₃ := disjointTripleChartThird n (b, c) (c, d) (d, e)
  have h₁ : f₁ ≫ productArrowTarget n b c = f₂ ≫ productArrowSource n c d := by
    apply (cancel_mono (normalizedDisjointInclusion n c)).mp
    simpa only [Category.assoc] using
      disjointTripleChart_first_middle n (b, c) (c, d) (d, e)
  have h₂ : f₂ ≫ productArrowTarget n c d = f₃ ≫ productArrowSource n d e := by
    apply (cancel_mono (normalizedDisjointInclusion n d)).mp
    simpa only [Category.assoc] using
      disjointTripleChart_second_middle n (b, c) (c, d) (d, e)
  let a : ProductArrow n (f₁ ≫ productArrowSource n b c)
      (f₁ ≫ productArrowTarget n b c) := ⟨f₁, by
    apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
      productArrowSource, productArrowTarget]⟩
  let z : ProductArrow n (f₁ ≫ productArrowTarget n b c)
      (f₂ ≫ productArrowTarget n c d) := ⟨f₂, by
    rw [h₁]
    apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
      productArrowSource, productArrowTarget]⟩
  let w : ProductArrow n (f₂ ≫ productArrowTarget n c d)
      (f₃ ≫ productArrowTarget n d e) := ⟨f₃, by
    rw [h₂]
    apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
      productArrowSource, productArrowTarget]⟩
  exact disjointTriple_associative_parameters n _ a z w
    (disjointTripleChartMap_first n _ _ _) (disjointTripleChartMap_second n _ _ _)
    (disjointTripleChartMap_third n _ _ _)

/-- Both global composites agree on the entire actual triple fiber product. -/
@[reassoc] theorem disjointCompositionMap_associative :
    disjointTripleLeftInsertion n ≫ disjointCompositionMap n =
      disjointTripleRightInsertion n ≫ disjointCompositionMap n := by
  apply (disjointTripleCover n).hom_ext
  rintro ⟨⟨⟨b, c⟩, ⟨d, e⟩⟩, ⟨f, g⟩⟩
  change disjointTripleChartMap n (b, c) (d, e) (f, g) ≫ _ =
    disjointTripleChartMap n (b, c) (d, e) (f, g) ≫ _
  by_cases h₁ : c = d
  · subst d
    by_cases h₂ : e = f
    · subst f
      exact disjointTripleChart_associative n b c e g
    · let _ := disjointTripleChart_empty_second n (b, c) (c, e) (f, g) h₂
      exact isInitialOfIsEmpty.hom_ext _ _
  · let _ := disjointTripleChart_empty_first n (b, c) (d, e) (f, g) h₁
    exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.CyclicCharacteristicAtlas
