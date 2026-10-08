/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleFullMember

/-!
# Actual chart inputs of four compatible infinity laws

Cancellation of the open Y-chart inclusion identifies the intermediate inputs
with the normalized inner outputs. No associativity or final-output equality
is used to obtain these five identities.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The five actual Y-chart input compatibilities on a common four-infinity domain. -/
theorem infinityTriple_commonInputs {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W)
    (f g h k : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (hf : f ≫ infinityGlobalDomain W = t ≫ integralCurveTriplePair W)
    (hg : g ≫ infinityGlobalDomain W = t ≫ integralCurveTripleLastPair W)
    (hh : h ≫ infinityGlobalDomain W = t ≫ integralCurveAddFirstPair W hΔ)
    (hk : k ≫ infinityGlobalDomain W = t ≫ integralCurveAddLastPair W hΔ) :
    f ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
        g ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) ∧
    h ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) =
        f ≫ infinityAdditionSpec W ∧
    h ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
        g ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) ∧
    k ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) =
        f ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) ∧
    k ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
        g ≫ infinityAdditionSpec W := by
  have hf₁ := congrArg (fun a => a ≫ pullback.fst
    (integralCurveStructure W) (integralCurveStructure W)) hf
  have hf₂ := congrArg (fun a => a ≫ pullback.snd
    (integralCurveStructure W) (integralCurveStructure W)) hf
  have hg₁ := congrArg (fun a => a ≫ pullback.fst
    (integralCurveStructure W) (integralCurveStructure W)) hg
  have hg₂ := congrArg (fun a => a ≫ pullback.snd
    (integralCurveStructure W) (integralCurveStructure W)) hg
  have hh₁ := congrArg (fun a => a ≫ pullback.fst
    (integralCurveStructure W) (integralCurveStructure W)) hh
  have hh₂ := congrArg (fun a => a ≫ pullback.snd
    (integralCurveStructure W) (integralCurveStructure W)) hh
  have hk₁ := congrArg (fun a => a ≫ pullback.fst
    (integralCurveStructure W) (integralCurveStructure W)) hk
  have hk₂ := congrArg (fun a => a ≫ pullback.snd
    (integralCurveStructure W) (integralCurveStructure W)) hk
  simp only [Category.assoc, infinityGlobalDomain_fst, infinityGlobalDomain_snd,
    integralCurveTripleLastPair_fst, integralCurveTripleLastPair_snd,
    integralCurveAddFirstPair_fst, integralCurveAddFirstPair_snd,
    integralCurveAddLastPair_fst, integralCurveAddLastPair_snd] at hf₁ hf₂ hg₁ hg₂ hh₁ hh₂ hk₁ hk₂
  have hfa := congrArg (fun a => a ≫ integralCurveAddition W hΔ) hf
  have hga := congrArg (fun a => a ≫ integralCurveAddition W hΔ) hg
  simp only [Category.assoc, infinityGlobalDomain_addition, infinityAdditionSpec] at hfa hga
  have hmid : f ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 1)).mp
    simpa only [Category.assoc, integralCurveTripleSecond] using hf₂.trans hg₁.symm
  have hleft : h ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 1)).mp
    simpa only [Category.assoc] using hh₁.trans hfa.symm
  have hthird : h ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 1)).mp
    simpa only [Category.assoc] using hh₂.trans hg₂.symm
  have hfirst : k ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 1)).mp
    simpa only [Category.assoc, integralCurveTripleFirst] using hk₁.trans hf₁.symm
  have hright : k ≫ Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 1)).mp
    simpa only [Category.assoc] using hk₂.trans hga.symm
  exact ⟨hmid, hleft, hthird, hfirst, hright⟩

/-- The actual outer infinity outputs are the two iterated global sums. -/
theorem infinityTriple_outerOutputs {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W)
    (h k : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (hh : h ≫ infinityGlobalDomain W = t ≫ integralCurveAddFirstPair W hΔ)
    (hk : k ≫ infinityGlobalDomain W = t ≫ integralCurveAddLastPair W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ =
        h ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 ∧
    t ≫ integralCurveTripleAddRight W hΔ =
        k ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  constructor
  · rw [integralCurveTripleAddLeft, ← Category.assoc, ← hh, Category.assoc,
      infinityGlobalDomain_addition]
  · rw [integralCurveTripleAddRight, ← Category.assoc, ← hk, Category.assoc,
      infinityGlobalDomain_addition]

end FLT.Mazur.WeierstrassIntegralChart
