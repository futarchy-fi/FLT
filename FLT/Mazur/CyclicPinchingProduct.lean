/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicProductDescent
public import FLT.Mazur.PinchingPullbackTransport

/-!
# The cyclic pinching pushout after affine parameter base change

Transport normalization descent and its endpoint equations to the exact
`Over.pullback` pinching span, for any commutative coefficient algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.CyclicPinchingProduct
open PinchingPullbackTransport CyclicProductNormalization PinchingChartBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
variable (n : ℕ) (hn : 2 ≤ n)
/-- The scheme normalization coproduct with its structure map. -/
def componentsOver : Over (Spec (.of K)) := Over.mk (componentsBase K n)
/-- Identify the scheme coproduct with the specified over-category coproduct. -/
def componentsIso : componentsOver K n ≅ PolygonPinching.components K n :=
  Over.isoMk (asIso (PolygonCyclicNormalizationFinite.comparison K n)) (by
    change PolygonCyclicNormalizationFinite.comparison K n ≫
      (PolygonPinching.components K n).hom = componentsBase K n
    apply Sigma.hom_ext
    intro i
    rw [ι_comp_sigmaComparison_assoc]
    change (PolygonPinching.componentι K n i).left ≫ _ = _
    rw [Over.w]
    simp [componentsBase])
/-- The normalization source after affine parameter base change. -/
def sourceIso : Over.mk (pullback.fst (parameter K S) (componentsBase K n)) ≅
    (Over.pullback (parameter K S)).obj (PolygonPinching.components K n) :=
  comparison (parameter K S) (componentsIso K n)
/-- The cyclic polygon after reversing the pullback convention. -/
def targetIso : Over.mk (pullback.fst (parameter K S) (PolygonCyclicAtlas.toBase K n hn)) ≅
    (Over.pullback (parameter K S)).obj (PolygonCyclicAtlas.polygon K n hn) :=
  swap (parameter K S) (PolygonCyclicAtlas.polygon K n hn)
@[reassoc] theorem normalization_comparison :
    (sourceIso K S n).hom.left ≫
      ((Over.pullback (parameter K S)).map (PolygonCyclicAtlas.normalization K n hn)).left =
    normalizationProduct K S n hn ≫ (targetIso K S n hn).hom.left := by
  apply pullback.hom_ext
  · simp [sourceIso, targetIso, componentsOver, swap, PolygonCyclicAtlas.polygon, Over.pullback,
      componentsIso, PolygonCyclicNormalizationFinite.comparison_normalization]
  · simp [sourceIso, targetIso, componentsOver, swap, PolygonCyclicAtlas.polygon, Over.pullback]
@[reassoc] theorem endpoint_comparison (hpos : 0 < n) (j : Fin n) (b : Bool) :
    CyclicProductEndpoints.endpoint K S n j b ≫ (sourceIso K S n).hom.left =
      sectionMap (parameter K S) (PolygonPinching.endpoint K n hpos j b) := by
  have hi (i : Fin n) : Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) i ≫
      PolygonCyclicNormalizationFinite.comparison K n =
        (PolygonPinching.componentι K n i).left :=
    ι_comp_sigmaComparison (Over.forget (Spec (.of K)))
      (fun _ : Fin n ↦ PolygonPinching.component K) i
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceIso, comparison_fst, componentsOver, Over.mk_hom,
      CyclicProductEndpoints.endpoint_snd_assoc,
      sectionMap, pullback.lift_fst]
    cases b <;> simp only [CyclicProductEndpoints.originalEndpoint, Bool.false_eq_true,
      ↓reduceIte, finRotate_apply, componentsIso, Over.isoMk_hom_left, Over.mk_left, asIso_hom,
      Category.assoc, PolygonPinching.endpoint, PolygonPinching.componentι,
      PolygonCyclicAtlas.next_eq_rotate, Over.comp_left]
    all_goals rw [hi]; rfl
  · simp [sourceIso, componentsOver, sectionMap]
theorem exists_desc (hpos : 0 < n) {Y : Over (Spec (.of S))}
    (f : (Over.pullback (parameter K S)).obj (PolygonPinching.components K n) ⟶ Y)
    (q : (Over.pullback (parameter K S)).obj (PolygonPinching.nodes K n) ⟶ Y)
    (w : (Over.pullback (parameter K S)).map (PolygonPinching.toComponents K n hpos) ≫ f =
      (Over.pullback (parameter K S)).map (PolygonPinching.toNodes K n) ≫ q) :
    ∃! d : (Over.pullback (parameter K S)).obj (PolygonCyclicAtlas.polygon K n hn) ⟶ Y,
      (Over.pullback (parameter K S)).map (PolygonCyclicAtlas.normalization K n hn) ≫ d = f := by
  let h := (sourceIso K S n).hom.left ≫ f.left
  have hw (j : Fin n) : CyclicProductEndpoints.endpoint K S n j false ≫ h =
      CyclicProductEndpoints.endpoint K S n j true ≫ h := by
    dsimp [h]
    rw [endpoint_comparison_assoc K S n hpos, endpoint_comparison_assoc K S n hpos]
    exact input_condition K n (parameter K S) hpos f q w j
  obtain ⟨d, hd, hu⟩ := CyclicProductDescent.exists_desc K S n hn h hw
  have hb : d ≫ Y.hom = pullback.fst _ _ :=
    CyclicProductDescent.desc_toBase K S n hn h Y.hom (by
      dsimp [h]
      rw [Category.assoc, Over.w]
      exact (sourceIso K S n).hom.w) d hd
  let d' : Over.mk (pullback.fst (parameter K S) (PolygonCyclicAtlas.toBase K n hn)) ⟶ Y :=
    Over.homMk d hb
  refine ⟨(targetIso K S n hn).inv ≫ d', ?_, ?_⟩
  · apply (cancel_epi (sourceIso K S n).hom).mp
    apply Over.OverMorphism.ext
    change (sourceIso K S n).hom.left ≫ _ ≫ _ ≫ d = _
    rw [normalization_comparison_assoc]
    rw [← Category.assoc (targetIso K S n hn).hom.left, ← Over.comp_left,
      Iso.hom_inv_id, Over.id_left, Category.id_comp]
    exact hd
  · intro e he
    apply (cancel_epi (targetIso K S n hn).hom).mp
    apply Over.OverMorphism.ext
    change (targetIso K S n hn).hom.left ≫ e.left = _
    have hh : normalizationProduct K S n hn ≫
        ((targetIso K S n hn).hom.left ≫ e.left) = h := by
      rw [← normalization_comparison_assoc]
      change (sourceIso K S n).hom.left ≫ ( _ ≫ e).left = h
      rw [he]
    have heq := hu _ hh
    simpa only [Over.comp_left, ← Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp, d', Over.homMk_left] using heq

theorem isPushout (hpos : 0 < n) :
    IsPushout ((Over.pullback (parameter K S)).map (PolygonPinching.toComponents K n hpos))
      ((Over.pullback (parameter K S)).map (PolygonPinching.toNodes K n))
      ((Over.pullback (parameter K S)).map (PolygonCyclicAtlas.normalization K n hn))
      ((Over.pullback (parameter K S)).map (PolygonCyclicAtlas.nodes K n hn)) := by
  apply PinchingPushoutCriterion.isPushout_of_existsUnique
  · rw [← Functor.map_comp, ← Functor.map_comp, PolygonCyclicAtlas.cocone]
  · intro Y f q w
    exact exists_desc K S n hn hpos f q w
end FLT.Mazur.CyclicPinchingProduct
