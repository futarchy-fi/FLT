/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointQuotientReduction

/-!
# Recovering comparison parameters from global arrows

A map into the assembled arrow scheme whose endpoints lie in specified
normalized charts factors through their original comparison component.
Thus arbitrary global-arrow tests retain an actual compatible comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

instance disjointComparisonInclusion_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (disjointComparisonInclusion n b c) := by
  unfold disjointComparisonInclusion
  infer_instance

/-- Specified endpoint components force the entire arrow into their comparison component. -/
theorem disjointComparison_range_of_endpoints {T : Scheme} (b c : Bool)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
    (a : T ⟶ disjointComparisonArrows n)
    (hs : a ≫ disjointComparisonSource n = q ≫ normalizedDisjointInclusion n b)
    (ht : a ≫ disjointComparisonTarget n = r ≫ normalizedDisjointInclusion n c) :
    Set.range a ⊆ Set.range (disjointComparisonInclusion n b c) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨⟨d, e⟩, y, hy⟩ :=
    (sigmaOpenCover (fun p : Bool × Bool ↦ productSubgroupScheme n p.1 p.2)).exists_eq
      (a x)
  change disjointComparisonInclusion n d e y = a x at hy
  have hs' := congrArg (disjointComparisonSource n) hy
  have ht' := congrArg (disjointComparisonTarget n) hy
  change (disjointComparisonInclusion n d e ≫ disjointComparisonSource n) y =
    (a ≫ disjointComparisonSource n) x at hs'
  change (disjointComparisonInclusion n d e ≫ disjointComparisonTarget n) y =
    (a ≫ disjointComparisonTarget n) x at ht'
  rw [disjointComparisonInclusion_source, hs, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at hs'
  rw [disjointComparisonInclusion_target, ht, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at ht'
  have hd : d = b := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hs')
  have he : e = c := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp ht')
  subst d e
  exact ⟨y, hy⟩

/-- The original comparison parameter underlying a global arrow with specified endpoints. -/
def disjointComparisonRecover {T : Scheme} (b c : Bool)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
    (a : T ⟶ disjointComparisonArrows n)
    (hs : a ≫ disjointComparisonSource n = q ≫ normalizedDisjointInclusion n b)
    (ht : a ≫ disjointComparisonTarget n = r ≫ normalizedDisjointInclusion n c) :
    ProductArrow n q r := by
  let k := IsOpenImmersion.lift (disjointComparisonInclusion n b c) a
    (disjointComparison_range_of_endpoints n b c q r a hs ht)
  have hk : k ≫ disjointComparisonInclusion n b c = a :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨k, ?_⟩
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst]
    change k ≫ productArrowSource n b c = q
    apply (cancel_mono (normalizedDisjointInclusion n b)).mp
    rw [Category.assoc, ← disjointComparisonInclusion_source, ← Category.assoc, hk, hs]
  · simp only [Category.assoc, prod.lift_snd]
    change k ≫ productArrowTarget n b c = r
    apply (cancel_mono (normalizedDisjointInclusion n c)).mp
    rw [Category.assoc, ← disjointComparisonInclusion_target, ← Category.assoc, hk, ht]

/-- A global comparison arrow gives the actual original-family compatibility on every test. -/
theorem disjointComparison_unmarkedRelated {T : Scheme} (b c : Bool)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
    (a : T ⟶ disjointComparisonArrows n)
    (hs : a ≫ disjointComparisonSource n = q ≫ normalizedDisjointInclusion n b)
    (ht : a ≫ disjointComparisonTarget n = r ≫ normalizedDisjointInclusion n c) :
    UnmarkedRelated n b c q r :=
  ⟨productCompatibleTestComparison n b c q r
    (disjointComparisonRecover n b c q r a hs ht)⟩

end FLT.Mazur.CyclicCharacteristicAtlas
