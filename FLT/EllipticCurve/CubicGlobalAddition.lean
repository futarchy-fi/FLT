/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicFirstInputAddition

/-! # Global addition on the smooth Weierstrass cubic -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A chart inclusion in the second factor after arbitrary base change. -/
def chartRightBaseChangeInclusion {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : Bool) :
    pullback f (chartToBase W b) ⟶ pullback f (toBase W) :=
  pullback.map _ _ _ _ (𝟙 _) (sourceChart W b) (𝟙 _) (by simp) (by simp)

instance chartRightBaseChangeInclusion_isOpenImmersion
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : Bool) :
    IsOpenImmersion (chartRightBaseChangeInclusion W f b) := by
  unfold chartRightBaseChangeInclusion
  infer_instance

/-- The original two-chart cover in the second factor. -/
def chartRightBaseChangeCover {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    (pullback f (toBase W)).OpenCover :=
  (Scheme.Pullback.openCoverOfRight (sourceOpenCover W) f (toBase W)).copy Bool
    (fun b ↦ pullback f (chartToBase W b)) (chartRightBaseChangeInclusion W f) (Equiv.refl _)
    (fun b ↦ (pullback.congrHom (rfl : f = f) (sourceChart_toBase W b)).symm) (by
      intro b
      apply pullback.hom_ext <;>
        simp [chartRightBaseChangeInclusion, pullback.congrHom, sourceOpenCover] <;> rfl)

/-- The common chart overlap in the second factor after base change. -/
def chartOverlapRightBaseChangeMap {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : Bool) :
    pullback f (chartOverlapToBase W) ⟶ pullback f (chartToBase W b) :=
  pullback.map _ _ _ _ (𝟙 _) (chartOverlapMap W b) (𝟙 _) (by simp) (by simp)

theorem chartOverlap_rightBaseChange_isPullback
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    IsPullback (chartOverlapRightBaseChangeMap W f false)
      (chartOverlapRightBaseChangeMap W f true)
      (chartRightBaseChangeInclusion W f false) (chartRightBaseChangeInclusion W f true) := by
  apply (chartOverlap_baseChange_isPullback W f).of_iso
    (pullbackSymmetry (chartOverlapToBase W) f)
    (pullbackSymmetry (chartToBase W false) f)
    (pullbackSymmetry (chartToBase W true) f)
    (pullbackSymmetry (toBase W) f)
  all_goals
    apply pullback.hom_ext <;>
      simp [chartOverlapBaseChangeMap, chartOverlapRightBaseChangeMap,
        chartBaseChangeInclusion, chartRightBaseChangeInclusion, pullback.map, Category.assoc]

@[reassoc] theorem chartOverlapRightBaseChangeMap_spec (b c : Bool) :
    (pullbackSpecIso R (Ring W b) (Overlap W true)).inv ≫
      chartOverlapRightBaseChangeMap W (chartToBase W b) c ≫
        (pullbackSpecIso R (Ring W b) (Ring W c)).hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft :
          Ring W b →ₐ[R] Ring W b ⊗[R] Overlap W true)
        ((Algebra.TensorProduct.includeRight :
          Overlap W true →ₐ[R] Ring W b ⊗[R] Overlap W true).comp
            (chartOverlapAlg W c))).toRingHom) := by
  have hid : Spec.map (CommRingCat.ofHom (AlgHom.id R (Ring W b)).toRingHom) =
      𝟙 (chart W b) := by
    change Spec.map (𝟙 _) = _
    exact Spec.map_id _
  simpa only [chartOverlapRightBaseChangeMap, chartOverlapMap_eq_specMap, chartOverlapToBase,
    chartToBase, AlgHom.comp_id, hid] using
    (pullbackSpecIso_productMap (R := R) (AlgHom.id R (Ring W b)) (chartOverlapAlg W c))

theorem chartAdditionMorphism_second_overlap [W.IsElliptic] (b : Bool) :
    chartOverlapRightBaseChangeMap W (chartToBase W b) false ≫ chartAdditionMorphism W b false =
      chartOverlapRightBaseChangeMap W (chartToBase W b) true ≫ chartAdditionMorphism W b true := by
  apply (cancel_epi (pullbackSpecIso R (Ring W b) (Overlap W true)).inv).mp
  simp only [chartAdditionMorphism, chartOverlapRightBaseChangeMap_spec_assoc]
  exact (chartAddition_change_second W b
    (Algebra.TensorProduct.includeLeft : Ring W b →ₐ[R] Ring W b ⊗[R] Overlap W true)
    (Algebra.TensorProduct.includeRight : Overlap W true →ₐ[R] Ring W b ⊗[R] Overlap W true)).symm

@[reassoc] theorem chartBaseChangeInclusion_overlapRight (b c : Bool) :
    chartBaseChangeInclusion W (chartOverlapToBase W) b ≫
        chartOverlapRightBaseChangeMap W (toBase W) c =
      chartOverlapRightBaseChangeMap W (chartToBase W b) c ≫
        chartBaseChangeInclusion W (chartToBase W c) b := by
  apply pullback.hom_ext <;>
    simp [chartBaseChangeInclusion, chartOverlapRightBaseChangeMap, pullback.map, Category.assoc]

theorem fixedSecondAddition_overlap [W.IsElliptic] :
    chartOverlapRightBaseChangeMap W (toBase W) false ≫ fixedSecondAddition W false =
      chartOverlapRightBaseChangeMap W (toBase W) true ≫ fixedSecondAddition W true := by
  apply (chartBaseChangeCover W (chartOverlapToBase W)).hom_ext
  intro b
  change chartBaseChangeInclusion W (chartOverlapToBase W) b ≫ _ =
    chartBaseChangeInclusion W (chartOverlapToBase W) b ≫ _
  simp only [chartBaseChangeInclusion_overlapRight_assoc,
    fixedSecondAddition_restrict]
  exact chartAdditionMorphism_second_overlap W b

theorem fixedSecondAddition_pullback [W.IsElliptic] :
    pullback.fst (chartRightBaseChangeInclusion W (toBase W) false)
      (chartRightBaseChangeInclusion W (toBase W) true) ≫ fixedSecondAddition W false =
    pullback.snd _ _ ≫ fixedSecondAddition W true := by
  apply (cancel_epi (chartOverlap_rightBaseChange_isPullback W (toBase W)).isoPullback.hom).mp
  simpa only [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    using fixedSecondAddition_overlap W

theorem fixedSecondAddition_gluing [W.IsElliptic] (b c : Bool) :
    pullback.fst (chartRightBaseChangeInclusion W (toBase W) b)
      (chartRightBaseChangeInclusion W (toBase W) c) ≫ fixedSecondAddition W b =
    pullback.snd _ _ ≫ fixedSecondAddition W c := by
  by_cases h : b = c
  · subst c
    have he : pullback.fst (chartRightBaseChangeInclusion W (toBase W) b)
        (chartRightBaseChangeInclusion W (toBase W) b) =
        pullback.snd (chartRightBaseChangeInclusion W (toBase W) b)
          (chartRightBaseChangeInclusion W (toBase W) b) := by
      apply (cancel_mono (chartRightBaseChangeInclusion W (toBase W) b)).mp
      exact pullback.condition
    rw [he]
  · cases b <;> cases c
    · exact (h rfl).elim
    · exact fixedSecondAddition_pullback W
    · apply (cancel_epi (pullbackSymmetry
        (chartRightBaseChangeInclusion W (toBase W) false)
        (chartRightBaseChangeInclusion W (toBase W) true)).hom).mp
      simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
        using (fixedSecondAddition_pullback W).symm
    · exact (h rfl).elim

/-- Addition on the entire smooth cubic product, descended from the four chart formulas. -/
def addition [W.IsElliptic] : pullback (toBase W) (toBase W) ⟶ scheme W :=
  (chartRightBaseChangeCover W (toBase W)).glueMorphisms
    (fixedSecondAddition W) (fixedSecondAddition_gluing W)

@[reassoc (attr := simp)] theorem addition_restrict_second [W.IsElliptic] (c : Bool) :
    chartRightBaseChangeInclusion W (toBase W) c ≫ addition W = fixedSecondAddition W c :=
  (chartRightBaseChangeCover W (toBase W)).ι_glueMorphisms _ _ c

@[reassoc (attr := simp)] theorem addition_toBase [W.IsElliptic] :
    addition W ≫ toBase W = pullback.fst (toBase W) (toBase W) ≫ toBase W := by
  apply (chartRightBaseChangeCover W (toBase W)).hom_ext
  intro c
  change chartRightBaseChangeInclusion W (toBase W) c ≫ (addition W ≫ toBase W) =
    chartRightBaseChangeInclusion W (toBase W) c ≫
      (pullback.fst (toBase W) (toBase W) ≫ toBase W)
  rw [← Category.assoc, addition_restrict_second, fixedSecondAddition_toBase]
  simp [chartRightBaseChangeInclusion, pullback.map]

theorem chartPairInclusion_factor (b c : Bool) :
    chartPairInclusion W b c =
      chartBaseChangeInclusion W (chartToBase W c) b ≫
        chartRightBaseChangeInclusion W (toBase W) c := by
  apply pullback.hom_ext <;>
    simp [chartPairInclusion, chartBaseChangeInclusion, chartRightBaseChangeInclusion,
      pullback.map, Category.assoc]

@[reassoc (attr := simp)] theorem addition_restrict_pair [W.IsElliptic] (b c : Bool) :
    chartPairInclusion W b c ≫ addition W = chartAdditionMorphism W b c := by
  rw [chartPairInclusion_factor, Category.assoc, addition_restrict_second,
    fixedSecondAddition_restrict]

end WeierstrassCurve.CubicCharts
