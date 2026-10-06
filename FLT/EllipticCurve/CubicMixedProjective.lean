/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicMixedRegular
public import FLT.EllipticCurve.CubicMixedOpposite
public import FLT.EllipticCurve.CubicProjectiveNormalization

/-! # Projective comparison on the entire mixed input chart -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem mixed_projective_pullback [W.IsElliptic] (d : Bool) :
    pullback.fst
      (Spec.map (CommRingCat.ofHom (mixedAffineRestriction W).toRingHom))
      (Spec.map (CommRingCat.ofHom (projectiveAdditionRestriction W true false d).toRingHom)) ≫
        mixedAffineAddition W =
      pullback.snd _ _ ≫ projectiveAddition W true false d := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true false) (MixedAffineRing W))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true false)
          (ProjectiveAdditionRing W true false d)))) ≫ mixedAffineAddition W =
    pullback.snd _ _ ≫ projectiveAddition W true false d
  apply (cancel_epi (pullbackSpecIso (ChartPairRing W true false)
    (MixedAffineRing W) (ProjectiveAdditionRing W true false d)).inv).mp
  simp only [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  let D := MixedAffineRing W ⊗[ChartPairRing W true false] ProjectiveAdditionRing W true false d
  let l : MixedAffineRing W →ₐ[R] D :=
    (Algebra.TensorProduct.includeLeft :
      MixedAffineRing W →ₐ[ChartPairRing W true false] D).restrictScalars R
  let r : ProjectiveAdditionRing W true false d →ₐ[R] D :=
    (Algebra.TensorProduct.includeRight :
      ProjectiveAdditionRing W true false d →ₐ[ChartPairRing W true false] D).restrictScalars R
  have hi : l.comp (mixedAffineRestriction W) =
      r.comp (projectiveAdditionRestriction W true false d) := by
    apply AlgHom.ext
    intro x
    exact ((Algebra.TensorProduct.includeLeft :
      MixedAffineRing W →ₐ[ChartPairRing W true false] D).commutes x).trans
        ((Algebra.TensorProduct.includeRight :
          ProjectiveAdditionRing W true false d →ₐ[ChartPairRing W true false] D).commutes x).symm
  exact mixed_addition_agreement W l r hi

/-- The descended mixed-chart addition agrees with either normalized projective
law throughout its domain, by schematic density of finite first inputs. -/
theorem mixedChartAddition_projective [W.IsElliptic] (d : Bool) :
    Spec.map (CommRingCat.ofHom (projectiveAdditionRestriction W true false d).toRingHom) ≫
        mixedChartAddition W = projectiveAddition W true false d := by
  let j := Spec.map (CommRingCat.ofHom (mixedAffineRestriction W).toRingHom)
  let k := Spec.map (CommRingCat.ofHom (projectiveAdditionRestriction W true false d).toRingHom)
  have : IsOpenImmersion k :=
    IsOpenImmersion.of_isLocalization (projectiveAdditionDenominator W true false d)
  have : IsSchemeTheoreticallyDominant j := mixedAffineRestriction_schematic_dominance W
  have : IsSchemeTheoreticallyDominant (pullback.snd j k) := inferInstance
  refine hom_ext_of_schematic_dominance (toBase W) ?_ (pullback.snd j k) ?_
  · rw [Category.assoc, mixedChartAddition_toBase, projectiveAddition_toBase, ← Spec.map_comp]
    congr 1
  · change pullback.snd j k ≫ k ≫ mixedChartAddition W =
      pullback.snd j k ≫ projectiveAddition W true false d
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
    have hj : j ≫ mixedChartAddition W = mixedAffineAddition W :=
      mixedChartAddition_restrict W 0
    rw [hj]
    exact mixed_projective_pullback W d

theorem mixedChartAddition_after_projective [W.IsElliptic] (d : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : ProjectiveAdditionRing W true false d →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom
      (f.comp (projectiveAdditionRestriction W true false d)).toRingHom) ≫ mixedChartAddition W =
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ projectiveAddition W true false d := by
  change Spec.map (CommRingCat.ofHom (projectiveAdditionRestriction W true false d).toRingHom ≫
    CommRingCat.ofHom f.toRingHom) ≫ mixedChartAddition W = _
  rw [Spec.map_comp, Category.assoc, mixedChartAddition_projective]


/-- Any normalized projective formula on a mixed input domain is the descended addition. -/
theorem mixedChartAddition_normalized [W.IsElliptic] (d : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : ChartPairRing W true false →ₐ[R] S) (g : Ring W d →ₐ[R] S) (t : S)
    (hg : ∀ i, chartPointCoords W d g i = f (chartPairSum W true false i) * t) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ mixedChartAddition W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ sourceChart W d := by
  obtain ⟨k, hk, hs⟩ := projectiveAddition_factor_normalization W true false d f g t hg
  have h := mixedChartAddition_after_projective W d k
  rw [hk] at h
  unfold projectiveAddition at h
  rw [← Category.assoc, ← Spec.map_comp] at h
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ mixedChartAddition W =
    Spec.map (CommRingCat.ofHom (k.comp (projectiveAdditionSum W true false d)).toRingHom) ≫
      sourceChart W d at h
  rw [hs] at h
  exact h

/-- The same normalized projective comparison for the opposite mixed input chart. -/
theorem oppositeMixedAddition_normalized [W.IsElliptic] (d : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : ChartPairRing W false true →ₐ[R] S) (g : Ring W d →ₐ[R] S) (t : S)
    (hg : ∀ i, chartPointCoords W d g i = f (chartPairSum W false true i) * t) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ oppositeMixedAddition W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ sourceChart W d := by
  have hn (i : Fin 3) : chartPointCoords W d g i =
      (f.comp (mixedPairSwap W).toAlgHom) (chartPairSum W true false i) * (-t) := by
    have h := congrArg f (congrFun (chartPairSum_swap W true false) i)
    change f (mixedPairSwap W (chartPairSum W true false i)) =
      f (-chartPairSum W false true i) at h
    rw [map_neg] at h
    change chartPointCoords W d g i =
      f (mixedPairSwap W (chartPairSum W true false i)) * (-t)
    rw [h, neg_mul_neg]
    exact hg i
  unfold oppositeMixedAddition
  rw [← Category.assoc, ← Spec.map_comp]
  exact mixedChartAddition_normalized W d (f.comp (mixedPairSwap W).toAlgHom) g (-t) hn

end WeierstrassCurve.CubicCharts
