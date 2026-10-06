/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicChartAddition

/-! # Descent in the first input of the cubic addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The two coordinate maps to the common overlap in infinity coordinates. -/
def chartOverlapAlg : ∀ b, Ring W b →ₐ[R] Overlap W true
  | false => changeChart W true
  | true => IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)

theorem chartOverlapMap_eq_specMap (b : Bool) :
    chartOverlapMap W b = Spec.map (CommRingCat.ofHom (chartOverlapAlg W b).toRingHom) := by
  cases b <;> rfl

@[reassoc] theorem chartOverlapBaseChangeMap_spec (b c : Bool) :
    (pullbackSpecIso R (Overlap W true) (Ring W c)).inv ≫
      chartOverlapBaseChangeMap W (chartToBase W c) b ≫
        (pullbackSpecIso R (Ring W b) (Ring W c)).hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
        ((Algebra.TensorProduct.includeLeft :
          Overlap W true →ₐ[R] Overlap W true ⊗[R] Ring W c).comp (chartOverlapAlg W b))
        (Algebra.TensorProduct.includeRight :
          Ring W c →ₐ[R] Overlap W true ⊗[R] Ring W c)).toRingHom) := by
  have hid : Spec.map (CommRingCat.ofHom (AlgHom.id R (Ring W c)).toRingHom) =
      𝟙 (chart W c) := by
    change Spec.map (𝟙 _) = _
    exact Spec.map_id _
  simpa only [chartOverlapBaseChangeMap, chartOverlapMap_eq_specMap, chartOverlapToBase,
    chartToBase, AlgHom.comp_id, hid] using
    (pullbackSpecIso_productMap (R := R) (chartOverlapAlg W b) (AlgHom.id R (Ring W c)))

theorem chartAdditionMorphism_first_overlap [W.IsElliptic] (c : Bool) :
    chartOverlapBaseChangeMap W (chartToBase W c) false ≫ chartAdditionMorphism W false c =
      chartOverlapBaseChangeMap W (chartToBase W c) true ≫ chartAdditionMorphism W true c := by
  apply (cancel_epi (pullbackSpecIso R (Overlap W true) (Ring W c)).inv).mp
  simp only [chartAdditionMorphism, chartOverlapBaseChangeMap_spec_assoc]
  exact (chartAddition_change_first W c
    (Algebra.TensorProduct.includeLeft : Overlap W true →ₐ[R] Overlap W true ⊗[R] Ring W c)
    (Algebra.TensorProduct.includeRight : Ring W c →ₐ[R] Overlap W true ⊗[R] Ring W c)).symm

theorem chartAdditionMorphism_first_pullback [W.IsElliptic] (c : Bool) :
    pullback.fst (chartBaseChangeInclusion W (chartToBase W c) false)
      (chartBaseChangeInclusion W (chartToBase W c) true) ≫ chartAdditionMorphism W false c =
    pullback.snd _ _ ≫ chartAdditionMorphism W true c := by
  apply (cancel_epi (chartOverlap_baseChange_isPullback W (chartToBase W c)).isoPullback.hom).mp
  simpa only [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    using chartAdditionMorphism_first_overlap W c

theorem chartAdditionMorphism_first_gluing [W.IsElliptic] (c b d : Bool) :
    pullback.fst (chartBaseChangeInclusion W (chartToBase W c) b)
      (chartBaseChangeInclusion W (chartToBase W c) d) ≫ chartAdditionMorphism W b c =
    pullback.snd _ _ ≫ chartAdditionMorphism W d c := by
  by_cases h : b = d
  · subst d
    have he : pullback.fst (chartBaseChangeInclusion W (chartToBase W c) b)
        (chartBaseChangeInclusion W (chartToBase W c) b) =
        pullback.snd (chartBaseChangeInclusion W (chartToBase W c) b)
          (chartBaseChangeInclusion W (chartToBase W c) b) := by
      apply (cancel_mono (chartBaseChangeInclusion W (chartToBase W c) b)).mp
      exact pullback.condition
    rw [he]
  · cases b <;> cases d
    · exact (h rfl).elim
    · exact chartAdditionMorphism_first_pullback W c
    · apply (cancel_epi (pullbackSymmetry
        (chartBaseChangeInclusion W (chartToBase W c) false)
        (chartBaseChangeInclusion W (chartToBase W c) true)).hom).mp
      simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
        using (chartAdditionMorphism_first_pullback W c).symm
    · exact (h rfl).elim

/-- Addition with arbitrary first input and second input in one chosen chart. -/
def fixedSecondAddition [W.IsElliptic] (c : Bool) :
    pullback (toBase W) (chartToBase W c) ⟶ scheme W :=
  (chartBaseChangeCover W (chartToBase W c)).glueMorphisms
    (fun b ↦ chartAdditionMorphism W b c) (chartAdditionMorphism_first_gluing W c)

@[reassoc (attr := simp)] theorem fixedSecondAddition_restrict [W.IsElliptic] (b c : Bool) :
    chartBaseChangeInclusion W (chartToBase W c) b ≫ fixedSecondAddition W c =
      chartAdditionMorphism W b c :=
  (chartBaseChangeCover W (chartToBase W c)).ι_glueMorphisms _ _ b

@[reassoc (attr := simp)] theorem fixedSecondAddition_toBase [W.IsElliptic] (c : Bool) :
    fixedSecondAddition W c ≫ toBase W =
      pullback.fst (toBase W) (chartToBase W c) ≫ toBase W := by
  apply (chartBaseChangeCover W (chartToBase W c)).hom_ext
  intro b
  change chartBaseChangeInclusion W (chartToBase W c) b ≫ (fixedSecondAddition W c ≫ toBase W) =
    chartBaseChangeInclusion W (chartToBase W c) b ≫
      (pullback.fst (toBase W) (chartToBase W c) ≫ toBase W)
  rw [← Category.assoc, fixedSecondAddition_restrict, chartAdditionMorphism_toBase]
  simp [chartBaseChangeInclusion, pullback.map, Category.assoc]

end WeierstrassCurve.CubicCharts
