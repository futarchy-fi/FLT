/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualTransitionDescent

/-!
# Opposite-characteristic reconstruction on arbitrary comparison tests

The reconstructed morphism has the required value on every test compatible
with a parameter in the original chart. Equality is detected on the actual
pullback fppf cover, so this retains scheme-theoretic comparison data.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) {Y : Scheme}
  (f : normalizedLocus n (!b) ⟶ Y)
  (hf : productArrowSource n (!b) (!b) ≫ f = productArrowTarget n (!b) (!b) ≫ f)

/-- Reconstructed invariants agree with every original-chart parameter related to the test. -/
theorem residualTransitionDescend_on_test {T : Scheme}
    (p : T ⟶ (transitionOpen n b).toScheme) (q : T ⟶ normalizedLocus n (!b))
    (h : UnmarkedRelated n b (!b) (p ≫ (transitionOpen n b).ι) q) :
    p ≫ residualTransitionDescend n b f hf = q ≫ f := by
  apply SchemeFppfFamily.cover_hom_ext ((transitionCover n b).pullback₁ p)
  intro i
  let l := pullback.fst p ((transitionCover n b).f i)
  let r := pullback.snd p ((transitionCover n b).f i)
  have hi := UnmarkedRelated.baseChange n (transition_unmarkedRelated n b i) r
  have hp : r ≫ transitionSource n b i = l ≫ p ≫ (transitionOpen n b).ι := by
    dsimp only [transitionSource]
    rw [← Category.assoc, ← pullback.condition]
    simp only [Category.assoc, l]
  rw [hp] at hi
  have ht := UnmarkedRelated.baseChange n h l
  have he := residual_invariant_on_test n b f hf _ _ (UnmarkedRelated.trans n hi ht)
  change l ≫ p ≫ residualTransitionDescend n b f hf = l ≫ q ≫ f
  rw [← Category.assoc, pullback.condition, Category.assoc,
    residualTransitionDescend_fac]
  simpa only [Category.assoc] using he

/-- The reconstructed map retains every same-chart comparison on the opposite overlap. -/
theorem residualTransitionDescend_invariant {T : Scheme}
    (p q : T ⟶ (transitionOpen n b).toScheme)
    (h : UnmarkedRelated n b b
      (p ≫ (transitionOpen n b).ι) (q ≫ (transitionOpen n b).ι)) :
    p ≫ residualTransitionDescend n b f hf =
      q ≫ residualTransitionDescend n b f hf := by
  apply SchemeFppfFamily.cover_hom_ext ((transitionCover n b).pullback₁ p)
  intro i
  let l := pullback.fst p ((transitionCover n b).f i)
  let r := pullback.snd p ((transitionCover n b).f i)
  have hi := UnmarkedRelated.baseChange n (transition_unmarkedRelated n b i) r
  have hp : r ≫ transitionSource n b i = l ≫ p ≫ (transitionOpen n b).ι := by
    dsimp only [transitionSource]
    rw [← Category.assoc, ← pullback.condition]
    simp only [Category.assoc, l]
  rw [hp] at hi
  have ht := UnmarkedRelated.trans n hi (UnmarkedRelated.baseChange n h l)
  have he := residualTransitionDescend_on_test n b f hf (l ≫ q)
    (r ≫ transitionTarget n b i) (by
      simpa only [Category.assoc] using UnmarkedRelated.symm n ht)
  change l ≫ p ≫ residualTransitionDescend n b f hf =
    l ≫ q ≫ residualTransitionDescend n b f hf
  rw [← Category.assoc, pullback.condition, Category.assoc,
    residualTransitionDescend_fac]
  simpa only [Category.assoc] using he.symm

/-- Reconstruction commutes with postcomposition of the original invariant morphism. -/
@[reassoc] theorem residualTransitionDescend_comp {Z : Scheme} (g : Y ⟶ Z) :
    residualTransitionDescend n b f hf ≫ g =
      residualTransitionDescend n b (f ≫ g) (by simp only [← Category.assoc, hf]) := by
  apply residualTransitionDescend_unique
  intro i
  rw [← Category.assoc, residualTransitionDescend_fac, Category.assoc]

end FLT.Mazur.CyclicCharacteristicAtlas
