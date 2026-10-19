/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointGroupoidPresheaf
public import FLT.Mazur.CyclicCharacteristicQuotientUnmarkedDescent

/-!
# Reducing the full groupoid quotient problem to the residual quotient relation

Invariance of the actual global arrow scheme is exactly invariance under all
original compatible comparisons. Thus every such invariant factors uniquely
through the finite relabeling quotient with the residual relation retained.
This does not assert representability of the residual quotient.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme} (f : normalizedDisjointSource n ⟶ Y)

/-- The global scheme equation is exactly invariance under every original comparison. -/
theorem disjointComparison_invariant_iff :
    disjointComparisonSource n ≫ f = disjointComparisonTarget n ≫ f ↔
      UnmarkedInvariant n (fun b ↦ normalizedDisjointInclusion n b ≫ f) := by
  constructor
  · intro h T b c q r hi
    obtain ⟨i⟩ := hi
    let a : ProductArrow n q r := productCompatibleParameter n b c q r i
    have he := congrArg (fun k ↦ a.val ≫ disjointComparisonInclusion n b c ≫ k) h
    rw [disjointComparisonInclusion_source_assoc,
      disjointComparisonInclusion_target_assoc] at he
    simpa only [← Category.assoc, productArrow_source, productArrow_target] using! he
  · intro h
    apply Sigma.hom_ext
    intro p
    change disjointComparisonInclusion n p.1 p.2 ≫ (disjointComparisonSource n ≫ f) =
      disjointComparisonInclusion n p.1 p.2 ≫ (disjointComparisonTarget n ≫ f)
    rw [disjointComparisonInclusion_source_assoc, disjointComparisonInclusion_target_assoc]
    exact h _ p.1 p.2 (productArrowSource n p.1 p.2) (productArrowTarget n p.1 p.2)
      ⟨productCompatibleTestComparison n p.1 p.2 _ _ (productUniversalArrow n p.1 p.2)⟩

/-- Factorization through the assembled finite quotient is detected on the original charts. -/
theorem disjointQuotient_factor_iff (k : normalizedDisjointQuotient n ⟶ Y) :
    normalizedDisjointQuotientMap n ≫ k = f ↔
      ∀ b, quotientUnmarkedPullback n k b = normalizedDisjointInclusion n b ≫ f := by
  constructor
  · intro h b
    have he := congrArg (normalizedDisjointInclusion n b ≫ ·) h
    simpa only [normalizedDisjointInclusion_quotientMap_assoc, quotientUnmarkedPullback] using he
  · intro h
    apply Sigma.hom_ext
    intro b
    change normalizedDisjointInclusion n b ≫ (normalizedDisjointQuotientMap n ≫ k) =
      normalizedDisjointInclusion n b ≫ f
    rw [normalizedDisjointInclusion_quotientMap_assoc]
    exact h b

/-- The full scheme coequalizer problem reduces to the genuine residual quotient relation. -/
theorem disjointComparison_invariant_iff_quotient_desc :
    disjointComparisonSource n ≫ f = disjointComparisonTarget n ≫ f ↔
      ∃! k : normalizedDisjointQuotient n ⟶ Y,
        normalizedDisjointQuotientMap n ≫ k = f ∧ QuotientUnmarkedInvariant n k := by
  rw [disjointComparison_invariant_iff, unmarkedInvariant_iff_quotient_desc]
  simp_rw [disjointQuotient_factor_iff]

end FLT.Mazur.CyclicCharacteristicAtlas
