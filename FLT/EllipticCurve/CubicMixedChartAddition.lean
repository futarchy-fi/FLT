/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicMixedGluing

/-! # Addition on the entire mixed input chart by descent -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The old affine addition and its projective extension on the mixed source cover. -/
def mixedAdditionPiece [W.IsElliptic] (i : Fin 2) : mixedAdditionOpen W i ⟶ scheme W := by
  refine Fin.cases (mixedAffineAddition W) ?_ i
  intro j
  exact Fin.cases (projectiveAddition W true false false) (fun k ↦ Fin.elim0 k) j

private theorem mixed_addition_pullback [W.IsElliptic] :
    pullback.fst (mixedAdditionInclusion W 0) (mixedAdditionInclusion W 1) ≫
        mixedAdditionPiece W 0 =
      pullback.snd _ _ ≫ mixedAdditionPiece W 1 := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true false) (MixedAffineRing W))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true false)
          (ProjectiveAdditionRing W true false false)))) ≫ mixedAffineAddition W =
    pullback.snd _ _ ≫ projectiveAddition W true false false
  apply (cancel_epi (pullbackSpecIso (ChartPairRing W true false)
    (MixedAffineRing W) (ProjectiveAdditionRing W true false false)).inv).mp
  simp only [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  let D := MixedAffineRing W ⊗[ChartPairRing W true false] ProjectiveAdditionRing W true false false
  let l : MixedAffineRing W →ₐ[R] D :=
    (Algebra.TensorProduct.includeLeft :
      MixedAffineRing W →ₐ[ChartPairRing W true false] D).restrictScalars R
  let r : ProjectiveAdditionRing W true false false →ₐ[R] D :=
    (Algebra.TensorProduct.includeRight :
      ProjectiveAdditionRing W true false false →ₐ[ChartPairRing W true false] D).restrictScalars R
  have hi : l.comp (mixedAffineRestriction W) =
      r.comp (projectiveAdditionRestriction W true false false) := by
    apply AlgHom.ext
    intro x
    have hl := (Algebra.TensorProduct.includeLeft :
      MixedAffineRing W →ₐ[ChartPairRing W true false] D).commutes x
    have hr := (Algebra.TensorProduct.includeRight :
      ProjectiveAdditionRing W true false false →ₐ[ChartPairRing W true false] D).commutes x
    exact hl.trans hr.symm
  exact mixed_addition_agreement W l r hi

theorem mixedAdditionPiece_gluing [W.IsElliptic] (i j : Fin 2) :
    pullback.fst (mixedAdditionInclusion W i) (mixedAdditionInclusion W j) ≫
        mixedAdditionPiece W i =
      pullback.snd _ _ ≫ mixedAdditionPiece W j := by
  wlog hij : i ≤ j generalizing i j
  · apply (cancel_epi
      (pullbackSymmetry (mixedAdditionInclusion W j) (mixedAdditionInclusion W i)).hom).mp
    have hji := this j i (le_of_not_ge hij)
    simpa only [pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc] using hji.symm
  by_cases he : i = j
  · subst j
    have hh : pullback.fst (mixedAdditionInclusion W i) (mixedAdditionInclusion W i) =
        pullback.snd (mixedAdditionInclusion W i) (mixedAdditionInclusion W i) := by
      apply (cancel_mono (mixedAdditionInclusion W i)).mp
      exact pullback.condition
    rw [hh]
  · have hlt : i < j := lt_of_le_of_ne hij he
    fin_cases i <;> fin_cases j <;> norm_num at hlt
    exact mixed_addition_pullback W

/-- Addition on the whole infinity-chart times ordinary-affine-chart product. -/
def mixedChartAddition [W.IsElliptic] :
    Spec (.of (ChartPairRing W true false)) ⟶ scheme W :=
  (mixedAdditionCover W).glueMorphisms (mixedAdditionPiece W) (mixedAdditionPiece_gluing W)

@[reassoc (attr := simp)] theorem mixedChartAddition_restrict [W.IsElliptic] (i : Fin 2) :
    mixedAdditionInclusion W i ≫ mixedChartAddition W = mixedAdditionPiece W i :=
  (mixedAdditionCover W).ι_glueMorphisms _ _ i

private theorem spec_algebraMap_comp {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R A B).symm

theorem mixedAdditionPiece_toBase [W.IsElliptic] (i : Fin 2) :
    mixedAdditionPiece W i ≫ toBase W = mixedAdditionInclusion W i ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartPairRing W true false))) := by
  fin_cases i
  · exact (mixedAffineAddition_toBase W).trans
      (spec_algebraMap_comp (R := R) (A := ChartPairRing W true false)
        (B := MixedAffineRing W)).symm
  · exact (projectiveAddition_toBase W true false false).trans
      (spec_algebraMap_comp (R := R) (A := ChartPairRing W true false)
        (B := ProjectiveAdditionRing W true false false)).symm

@[reassoc (attr := simp)] theorem mixedChartAddition_toBase [W.IsElliptic] :
    mixedChartAddition W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartPairRing W true false))) := by
  apply (mixedAdditionCover W).hom_ext
  intro i
  change mixedAdditionInclusion W i ≫ (mixedChartAddition W ≫ toBase W) =
    mixedAdditionInclusion W i ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartPairRing W true false)))
  rw [← Category.assoc, mixedChartAddition_restrict, mixedAdditionPiece_toBase]

/-- The descended mixed addition on the categorical product of input charts. -/
def mixedChartAdditionMorphism [W.IsElliptic] :
    pullback (chartToBase W true) (chartToBase W false) ⟶ scheme W :=
  (pullbackSpecIso R (Ring W true) (Ring W false)).hom ≫ mixedChartAddition W

@[reassoc] theorem mixedChartAddition_infinity [W.IsElliptic] :
    zeroAffineSection W ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ChartPairRing W true false)
        (ProjectiveAdditionRing W true false false))) ≫ mixedChartAddition W = affineChart W := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap (ChartPairRing W true false)
        (ProjectiveAdditionRing W true false false))) ≫ mixedChartAddition W =
      projectiveAddition W true false false := mixedChartAddition_restrict W 1
  exact (congrArg (fun k ↦ zeroAffineSection W ≫ k) h).trans (zeroAffineSection_addition W)

end WeierstrassCurve.CubicCharts
