/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryGlobalDomains
public import FLT.Mazur.WeierstrassReciprocalTripleSchemes
public import FLT.Mazur.WeierstrassReciprocalGlobalDomains
public import FLT.Mazur.WeierstrassSmoothFormulaComparison

/-!
# Global associativity on reciprocal outer domains

Ordinary inner charts and reciprocal outer charts give equal actual
iterated sums, including the locus where their output z-coordinate is not a unit.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Actual iterated sums agree on ordinary-inner, reciprocal-outer domains. -/
theorem smoothFactorTripleAdd_reciprocals {X : Scheme.{u}}
    (t : X ⟶ smoothFactorTriple W) (b c d e : Bool)
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (ordinaryIndex c)))
    (h : X ⟶ Spec (additionChartRing W (reciprocalIndex d)))
    (k : X ⟶ Spec (additionChartRing W (reciprocalIndex e)))
    (hf : f ≫ ordinaryGlobalDomain W b =
      t ≫ smoothFactorTriplePair W ≫ smoothFactorsInclusion W)
    (hg : g ≫ ordinaryGlobalDomain W c =
      t ≫ smoothFactorTripleLastPair W ≫ smoothFactorsInclusion W)
    (hh : h ≫ reciprocalGlobalDomain W d =
      t ≫ smoothFactorAddFirstPair W ≫ smoothFactorsInclusion W)
    (hk : k ≫ reciprocalGlobalDomain W e =
      t ≫ smoothFactorAddLastPair W ≫ smoothFactorsInclusion W) :
    t ≫ smoothFactorTripleAddLeft W =
      t ≫ smoothFactorTripleAddRight W := by
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
    reciprocalGlobalDomain_fst, reciprocalGlobalDomain_snd,
    smoothFactorsInclusion_fst, smoothFactorsInclusion_snd,
    smoothFactorTripleLastPair_fst_assoc, smoothFactorTripleLastPair_snd_assoc,
    smoothFactorAddFirstPair_fst_assoc, smoothFactorAddFirstPair_snd_assoc,
    smoothFactorAddLastPair_fst_assoc, smoothFactorAddLastPair_snd_assoc]
    at hf₁ hf₂ hg₁ hg₂ hh₁ hh₂ hk₁ hk₂
  have hfa := (smoothFactorAddition_ordinary W (t ≫ smoothFactorTriplePair W) b f hf).symm
  have hga := (smoothFactorAddition_ordinary W (t ≫ smoothFactorTripleLastPair W) c g hg).symm
  simp only [Category.assoc] at hfa hga
  have hmid : f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W c).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc, smoothFactorTripleSecond] using hf₂.trans hg₁.symm
  have hleft : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W d).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using hh₁.trans hfa.symm
  have hthird : h ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W d).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryInputRight W c).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using hh₂.trans hg₂.symm
  have hfirst : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputLeft W e).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc, smoothFactorTripleFirst] using hk₁.trans hf₁.symm
  have hright : k ≫ Spec.map (CommRingCat.ofHom (reciprocalInputRight W e).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W c).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using hk₂.trans hga.symm
  have heq := congrArg (fun a => a ≫ integralCurveChart W 1)
    (reciprocalTriple_commonScheme W b c d e f g h k hmid hleft hthird hfirst hright)
  have hha := smoothFactorAddition_reciprocal W (t ≫ smoothFactorAddFirstPair W) d h hh
  have hka := smoothFactorAddition_reciprocal W (t ≫ smoothFactorAddLastPair W) e k hk
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simpa only [smoothFactorTripleAddLeft, smoothFactorTripleAddRight, Category.assoc] using
    hha.trans (heq.trans hka.symm)


end FLT.Mazur.WeierstrassIntegralChart
