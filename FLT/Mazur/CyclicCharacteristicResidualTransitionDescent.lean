/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointQuotientReduction
public import FLT.Mazur.CyclicCharacteristicTransitionSpan
public import FLT.Mazur.SchemeFppfFamilyFunctionDescent

/-!
# Reconstructing residual invariants on the opposite characteristic

A scheme morphism invariant under the full same-chart comparison descends
along the actual fppf transition cover to the opposite chart's overlap open.
This uses all compatible original-family comparisons on arbitrary tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) {Y : Scheme}
  (f : normalizedLocus n (!b) ⟶ Y)
  (hf : productArrowSource n (!b) (!b) ≫ f = productArrowTarget n (!b) (!b) ≫ f)

include hf in
/-- The full same-chart equation controls every actual compatible comparison on scheme tests. -/
theorem residual_invariant_on_test {T : Scheme}
    (q r : T ⟶ normalizedLocus n (!b)) (h : UnmarkedRelated n (!b) (!b) q r) :
    q ≫ f = r ≫ f := by
  obtain ⟨a⟩ := h
  let k : ProductArrow n q r := productCompatibleParameter n (!b) (!b) q r a
  have he := congrArg (k.val ≫ ·) hf
  simpa only [← Category.assoc, productArrow_source, productArrow_target] using he

/-- The opposite-chart parameters are related on every common transition-cover test. -/
theorem transitionTarget_related_on_test {T : Scheme}
    (i j : (transitionCover n b).I₀)
    (g : T ⟶ (transitionCover n b).X i) (h : T ⟶ (transitionCover n b).X j)
    (he : g ≫ (transitionCover n b).f i = h ≫ (transitionCover n b).f j) :
    UnmarkedRelated n (!b) (!b)
      (g ≫ transitionTarget n b i) (h ≫ transitionTarget n b j) := by
  have hs : g ≫ transitionSource n b i = h ≫ transitionSource n b j := by
    simp only [transitionSource, ← Category.assoc, he]
  have hi := UnmarkedRelated.baseChange n (transition_unmarkedRelated n b i) g
  have hj := UnmarkedRelated.baseChange n (transition_unmarkedRelated n b j) h
  rw [hs] at hi
  exact UnmarkedRelated.trans n hi (UnmarkedRelated.symm n hj)

include hf in
/-- The actual transition family has compatible values for every residual-invariant map. -/
theorem residualTransition_compatible {T : Scheme}
    (i j : (transitionCover n b).I₀)
    (g : T ⟶ (transitionCover n b).X i) (h : T ⟶ (transitionCover n b).X j)
    (he : g ≫ (transitionCover n b).f i = h ≫ (transitionCover n b).f j) :
    g ≫ transitionTarget n b i ≫ f = h ≫ transitionTarget n b j ≫ f := by
  simpa only [Category.assoc] using residual_invariant_on_test n b f hf _ _
    (transitionTarget_related_on_test n b i j g h he)

/-- The residual map reconstructed on the opposite characteristic's actual overlap open. -/
def residualTransitionDescend : (transitionOpen n b).toScheme ⟶ Y := by
  let _ := SchemeFppfFamily.effectiveEpiFamily (transitionCover n b)
  exact EffectiveEpiFamily.desc (transitionCover n b).X (transitionCover n b).f
    (fun i => transitionTarget n b i ≫ f)
    (fun {_} i j g h he => residualTransition_compatible n b f hf i j g h he)

/-- Reconstruction retains the specified maps on every original fppf transition source. -/
@[reassoc] theorem residualTransitionDescend_fac (i : (transitionCover n b).I₀) :
    (transitionCover n b).f i ≫ residualTransitionDescend n b f hf =
      transitionTarget n b i ≫ f := by
  let _ := SchemeFppfFamily.effectiveEpiFamily (transitionCover n b)
  exact EffectiveEpiFamily.fac (transitionCover n b).X (transitionCover n b).f
    (fun j => transitionTarget n b j ≫ f)
    (fun {_} j k g h he => residualTransition_compatible n b f hf j k g h he) i

/-- The original transition family determines the reconstructed map uniquely. -/
theorem residualTransitionDescend_unique (k : (transitionOpen n b).toScheme ⟶ Y)
    (hk : ∀ i, (transitionCover n b).f i ≫ k = transitionTarget n b i ≫ f) :
    k = residualTransitionDescend n b f hf := by
  apply SchemeFppfFamily.cover_hom_ext (transitionCover n b)
  intro i
  rw [hk, residualTransitionDescend_fac]

end FLT.Mazur.CyclicCharacteristicAtlas
