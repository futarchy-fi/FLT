/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryGlobalDomains
public import FLT.Mazur.WeierstrassAllOrdinaryTripleSchemes
public import FLT.Mazur.WeierstrassIntegralTripleProduct

/-!
# Associativity on actual ordinary triple domains

A map into the true triple product whose inner pairs factor through ordinary
charts and whose outer pairs factor through ordinary charts has equal iterated
sums. All comparison premises concern the actual inputs, not the outputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Local associativity on every compatible four ordinary charts on a common scheme domain. -/
theorem integralCurveTripleAdd_allOrdinary {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) (b c d e : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W (ordinaryIndex d)))
    (k : X ⟶ Spec (additionChartRing W (ordinaryIndex e)))
    (hf : f ≫ ordinaryGlobalDomain W b = t ≫ integralCurveTriplePair W)
    (hg : g ≫ ordinaryGlobalDomain W c = t ≫ integralCurveTripleLastPair W)
    (hh : h ≫ ordinaryGlobalDomain W d = t ≫ integralCurveAddFirstPair W hΔ)
    (hk : k ≫ ordinaryGlobalDomain W e = t ≫ integralCurveAddLastPair W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
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
  simp only [Category.assoc, ordinaryGlobalDomain_fst, ordinaryGlobalDomain_snd,
    integralCurveTripleLastPair_fst, integralCurveTripleLastPair_snd,
    integralCurveAddFirstPair_fst, integralCurveAddFirstPair_snd,
    integralCurveAddLastPair_fst, integralCurveAddLastPair_snd] at hf₁ hf₂ hg₁ hg₂ hh₁ hh₂ hk₁ hk₂
  have hfa := congrArg (fun a => a ≫ integralCurveAddition W hΔ) hf
  have hga := congrArg (fun a => a ≫ integralCurveAddition W hΔ) hg
  simp only [Category.assoc, ordinaryGlobalDomain_addition] at hfa hga
  have hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc, integralCurveTripleSecond] using hf₂.trans hg₁.symm
  have hleft : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W d).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using hh₁.trans hfa.symm
  have hthird : h ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W d).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using hh₂.trans hg₂.symm
  have hfirst : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W e).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc, integralCurveTripleFirst] using hk₁.trans hf₁.symm
  have hright : k ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using hk₂.trans hga.symm
  have heq := congrArg (fun a => a ≫ integralCurveChart W 2)
    (allOrdinaryTriple_commonScheme W b c d e f g h k hmid hleft hthird hfirst hright)
  have hha := congrArg (fun a => a ≫ integralCurveAddition W hΔ) hh
  have hka := congrArg (fun a => a ≫ integralCurveAddition W hΔ) hk
  simp only [Category.assoc, ordinaryGlobalDomain_addition] at hha hka heq
  exact hha.symm.trans (heq.trans hka)

end FLT.Mazur.WeierstrassIntegralChart
