/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicAdditionOverlap
public import FLT.EllipticCurve.CubicMixedAddition

/-! # Addition on the entire ordinary input chart product

The four local chord constructions descend along their open cover. This
constructs addition for two ordinary affine inputs, including sums at infinity.
Inputs outside that chart and the global group axioms are not constructed here. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

private theorem agreement_of_tensor (C A B : Type u) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] {T : Scheme.{u}}
    (p : Spec (.of A) ⟶ T) (q : Spec (.of B) ⟶ T)
    (h : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] B).toRingHom) ≫ p =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).toRingHom) ≫ q) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap C A)))
        (Spec.map (CommRingCat.ofHom (algebraMap C B))) ≫ p =
      pullback.snd _ _ ≫ q := by
  apply (cancel_epi (pullbackSpecIso C A B).inv).mp
  simp only [pullbackSpecIso_inv_fst_assoc,
    pullbackSpecIso_inv_snd_assoc]
  exact h

/-- The four already constructed local additions, indexed by the source cover. -/
def affineAdditionPiece (i : Fin 4) : affineAdditionOpen W i ⟶ scheme W := by
  refine Fin.cases (secantAddition W) ?_ i
  intro j
  refine Fin.cases (tangentAddition W) ?_ j
  intro k
  refine Fin.cases (verticalAddition W false) ?_ k
  intro l
  exact Fin.cases (verticalAddition W true) (fun m ↦ Fin.elim0 m) l

private theorem secant_vertical_pullback (b : Bool) :
    pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W))))
        (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W b)))) ≫
          secantAddition W =
      pullback.snd _ _ ≫ verticalAddition W b := by
  apply agreement_of_tensor (AffinePairRing W) (SecantRing W) (VerticalRing W b)
  let D := SecantRing W ⊗[AffinePairRing W] VerticalRing W b
  let l : SecantRing W →ₐ[R] D := (Algebra.TensorProduct.includeLeft :
    SecantRing W →ₐ[AffinePairRing W] D).restrictScalars R
  let r : VerticalRing W b →ₐ[R] D := (Algebra.TensorProduct.includeRight :
    VerticalRing W b →ₐ[AffinePairRing W] D).restrictScalars R
  have hi : l.comp (IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)) =
      r.comp (verticalRestriction W b) := by
    apply AlgHom.ext
    intro x
    have hl := (Algebra.TensorProduct.includeLeft :
      SecantRing W →ₐ[AffinePairRing W] D).commutes x
    have hr := (Algebra.TensorProduct.includeRight :
      VerticalRing W b →ₐ[AffinePairRing W] D).commutes x
    exact hl.trans hr.symm
  have hh := secant_vertical_agreement W b l r hi
  change Spec.map (CommRingCat.ofHom l.toRingHom) ≫ secantAddition W =
    Spec.map (CommRingCat.ofHom r.toRingHom) ≫ verticalAddition W b
  unfold secantAddition verticalAddition
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact hh

private theorem tangent_vertical_pullback (b : Bool) :
    pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (TangentRing W))))
        (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W b)))) ≫
          tangentAddition W =
      pullback.snd _ _ ≫ verticalAddition W b := by
  apply agreement_of_tensor (AffinePairRing W) (TangentRing W) (VerticalRing W b)
  let D := TangentRing W ⊗[AffinePairRing W] VerticalRing W b
  let l : TangentRing W →ₐ[R] D := (Algebra.TensorProduct.includeLeft :
    TangentRing W →ₐ[AffinePairRing W] D).restrictScalars R
  let r : VerticalRing W b →ₐ[R] D := (Algebra.TensorProduct.includeRight :
    VerticalRing W b →ₐ[AffinePairRing W] D).restrictScalars R
  have hi : l.comp (IsScalarTower.toAlgHom R (AffinePairRing W) (TangentRing W)) =
      r.comp (verticalRestriction W b) := by
    apply AlgHom.ext
    intro x
    have hl := (Algebra.TensorProduct.includeLeft :
      TangentRing W →ₐ[AffinePairRing W] D).commutes x
    have hr := (Algebra.TensorProduct.includeRight :
      VerticalRing W b →ₐ[AffinePairRing W] D).commutes x
    exact hl.trans hr.symm
  have hh := tangent_vertical_agreement W b l r hi
  change Spec.map (CommRingCat.ofHom l.toRingHom) ≫ tangentAddition W =
    Spec.map (CommRingCat.ofHom r.toRingHom) ≫ verticalAddition W b
  unfold tangentAddition verticalAddition
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact hh

/-- Compatibility on every canonical pullback in the four-piece cover. -/
theorem affineAdditionPiece_gluing (i j : Fin 4) :
    pullback.fst (affineAdditionInclusion W i) (affineAdditionInclusion W j) ≫
        affineAdditionPiece W i =
      pullback.snd _ _ ≫ affineAdditionPiece W j := by
  wlog hij : i ≤ j generalizing i j
  · apply (cancel_epi
      (pullbackSymmetry (affineAdditionInclusion W j) (affineAdditionInclusion W i)).hom).mp
    have hji := this j i (le_of_not_ge hij)
    simpa only [pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc] using hji.symm
  by_cases he : i = j
  · subst j
    have hh : pullback.fst (affineAdditionInclusion W i) (affineAdditionInclusion W i) =
        pullback.snd _ _ :=
      (cancel_mono (affineAdditionInclusion W i)).mp pullback.condition
    rw [hh]
  have hlt : i < j := by omega
  fin_cases i <;> fin_cases j <;> norm_num at hlt
  · exact agreement_of_tensor (AffinePairRing W) (SecantRing W) (TangentRing W)
      (secantAddition W) (tangentAddition W) (secant_tangent_agreement W)
  · exact secant_vertical_pullback W false
  · exact secant_vertical_pullback W true
  · exact tangent_vertical_pullback W false
  · exact tangent_vertical_pullback W true
  · exact agreement_of_tensor (AffinePairRing W) (VerticalRing W false) (VerticalRing W true)
      (verticalAddition W false) (verticalAddition W true) (vertical_addition_agreement W)

/-- Addition for all pairs of ordinary affine inputs, with values in the complete cubic. -/
def affineAddition [W.IsElliptic] : Spec (.of (AffinePairRing W)) ⟶ scheme W :=
  (affineAdditionCover W).glueMorphisms (affineAdditionPiece W) (affineAdditionPiece_gluing W)

@[reassoc (attr := simp)] theorem affineAddition_restrict [W.IsElliptic] (i : Fin 4) :
    affineAdditionInclusion W i ≫ affineAddition W = affineAdditionPiece W i :=
  (affineAdditionCover W).ι_glueMorphisms _ _ i

private theorem spec_algebraMap_comp (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.toAlgHom R A B).comp_algebraMap

@[reassoc] theorem affineAdditionPiece_toBase (i : Fin 4) :
    affineAdditionPiece W i ≫ toBase W =
      affineAdditionInclusion W i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AffinePairRing W))) := by
  fin_cases i
  · exact (secantAddition_toBase W).trans
      (spec_algebraMap_comp (R := R) (AffinePairRing W) (SecantRing W)).symm
  · exact (tangentAddition_toBase W).trans
      (spec_algebraMap_comp (R := R) (AffinePairRing W) (TangentRing W)).symm
  · exact (verticalAddition_toBase W false).trans
      (spec_algebraMap_comp (R := R) (AffinePairRing W) (VerticalRing W false)).symm
  · exact (verticalAddition_toBase W true).trans
      (spec_algebraMap_comp (R := R) (AffinePairRing W) (VerticalRing W true)).symm

@[reassoc (attr := simp)] theorem affineAddition_toBase [W.IsElliptic] :
    affineAddition W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (AffinePairRing W))) := by
  apply (affineAdditionCover W).hom_ext
  intro i
  change affineAdditionInclusion W i ≫ (affineAddition W ≫ toBase W) =
    affineAdditionInclusion W i ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (AffinePairRing W)))
  rw [← Category.assoc, affineAddition_restrict, affineAdditionPiece_toBase]

/-- The descended addition, expressed on the actual fiber product of ordinary charts. -/
def affineAdditionMorphism [W.IsElliptic] :
    pullback (chartToBase W false) (chartToBase W false) ⟶ scheme W :=
  (pullbackSpecIso R (Ring W false) (Ring W false)).hom ≫ affineAddition W

@[reassoc (attr := simp)] theorem affineAdditionMorphism_toBase [W.IsElliptic] :
    affineAdditionMorphism W ≫ toBase W =
      pullback.fst (chartToBase W false) (chartToBase W false) ≫ chartToBase W false := by
  unfold affineAdditionMorphism
  rw [Category.assoc, affineAddition_toBase]
  exact pullbackSpecIso_hom_base R (Ring W false) (Ring W false)

end WeierstrassCurve.CubicCharts
