/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityGluing

/-! # Addition on the whole product of infinity charts by descent -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

private theorem infinityCoverAddition_self [W.IsElliptic] (i : Option Bool) :
    pullback.fst ((infinityChartAdditionCover W).f i) ((infinityChartAdditionCover W).f i) ≫
        infinityCoverAddition W i =
      pullback.snd _ _ ≫ infinityCoverAddition W i := by
  have h : pullback.fst ((infinityChartAdditionCover W).f i)
      ((infinityChartAdditionCover W).f i) =
      pullback.snd ((infinityChartAdditionCover W).f i) ((infinityChartAdditionCover W).f i) := by
    apply (cancel_mono ((infinityChartAdditionCover W).f i)).mp
    exact pullback.condition
  rw [h]

theorem infinityCoverAddition_gluing [W.IsElliptic] (i j : Option Bool) :
    pullback.fst ((infinityChartAdditionCover W).f i) ((infinityChartAdditionCover W).f j) ≫
        infinityCoverAddition W i =
      pullback.snd _ _ ≫ infinityCoverAddition W j := by
  have flip (i j : Option Bool)
      (h : pullback.fst ((infinityChartAdditionCover W).f j)
          ((infinityChartAdditionCover W).f i) ≫ infinityCoverAddition W j =
        pullback.snd _ _ ≫ infinityCoverAddition W i) :
      pullback.fst ((infinityChartAdditionCover W).f i)
          ((infinityChartAdditionCover W).f j) ≫ infinityCoverAddition W i =
        pullback.snd _ _ ≫ infinityCoverAddition W j := by
    apply (cancel_epi (pullbackSymmetry
      ((infinityChartAdditionCover W).f j) ((infinityChartAdditionCover W).f i)).hom).mp
    simpa only [pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc] using h.symm
  cases i with
  | none =>
    cases j with
    | none => exact infinityCoverAddition_self W none
    | some b => exact infinityFiniteAddition_origin_pullback W b
  | some b =>
    cases j with
    | none => exact flip _ _ (infinityFiniteAddition_origin_pullback W b)
    | some c =>
      cases b <;> cases c
      · exact infinityCoverAddition_self W (some false)
      · exact infinityFiniteAddition_pullback W
      · exact flip _ _ (infinityFiniteAddition_pullback W)
      · exact infinityCoverAddition_self W (some true)

/-- Addition on the entire product of infinity charts, obtained by gluing the
infinity-pair domain with both finite-input domains. -/
def infinityChartAddition [W.IsElliptic] :
    Spec (.of (ChartPairRing W true true)) ⟶ scheme W :=
  (infinityChartAdditionCover W).glueMorphisms
    (infinityCoverAddition W) (infinityCoverAddition_gluing W)

@[reassoc (attr := simp)] theorem infinityChartAddition_restrict [W.IsElliptic] (i : Option Bool) :
    (infinityChartAdditionCover W).f i ≫ infinityChartAddition W = infinityCoverAddition W i :=
  (infinityChartAdditionCover W).ι_glueMorphisms _ _ i

@[reassoc (attr := simp)] theorem infinityChartAddition_toBase [W.IsElliptic] :
    infinityChartAddition W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartPairRing W true true))) := by
  apply (infinityChartAdditionCover W).hom_ext
  intro i
  rw [← Category.assoc, infinityChartAddition_restrict, infinityCoverAddition_toBase]
  change Spec.map (CommRingCat.ofHom (algebraMap R (InfinityCoverRing W i))) =
    Spec.map (CommRingCat.ofHom (infinityCoverRestriction W i).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartPairRing W true true)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (infinityCoverRestriction W i).comp_algebraMap.symm

/-- Addition on the categorical product of the two infinity input charts. -/
def infinityChartAdditionMorphism [W.IsElliptic] :
    pullback (chartToBase W true) (chartToBase W true) ⟶ scheme W :=
  (pullbackSpecIso R (Ring W true) (Ring W true)).hom ≫ infinityChartAddition W

/-- The descended infinity-chart addition sends the pair of infinity sections to infinity. -/
@[reassoc] theorem infinityChartAddition_zeroPair [W.IsElliptic] :
    Spec.map (CommRingCat.ofHom (infinityPairOrigin W).toRingHom) ≫ infinityChartAddition W =
      infinity W := by
  have he : (infinityAdditionOrigin W).comp
      ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)) =
      infinityPairOrigin W := by
    apply AlgHom.ext
    intro x
    exact (infinityAdditionOrigin_restriction W _).trans (infinitySlopeOrigin_restriction W x)
  have h := congrArg (fun k ↦ infinityAdditionSection W ≫ k)
    (infinityChartAddition_restrict W none)
  change infinityAdditionSection W ≫
    (Spec.map (CommRingCat.ofHom
      ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)).toRingHom) ≫
        infinityChartAddition W) =
    infinityAdditionSection W ≫ infinityAddition W at h
  rw [infinityAdditionSection_addition] at h
  unfold infinityAdditionSection at h
  rw [← Category.assoc, ← Spec.map_comp] at h
  change Spec.map (CommRingCat.ofHom
    ((infinityAdditionOrigin W).comp
      ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W))).toRingHom) ≫
        infinityChartAddition W = infinity W at h
  rw [he] at h
  exact h

end WeierstrassCurve.CubicCharts
