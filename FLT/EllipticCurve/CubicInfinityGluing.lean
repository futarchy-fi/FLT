/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityProjective

/-! # Descending the infinity-pair comparisons from their dense projective opens -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- After a flat pullback of the infinity-addition domain, agreement with a
finite-input piece descends from the dense normalized projective formula. -/
theorem infinityFinite_addition_agreement_of_flat [W.IsElliptic] (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S] [Algebra (InfinityAdditionRing W) S]
    [IsScalarTower R (InfinityAdditionRing W) S] [Module.Flat (InfinityAdditionRing W) S]
    (g : InfinityFiniteRing W b →ₐ[R] S)
    (h : (IsScalarTower.toAlgHom R (InfinityAdditionRing W) S).comp
        ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)) =
      g.comp (infinityFiniteRestriction W b)) :
    Spec.map (CommRingCat.ofHom (algebraMap (InfinityAdditionRing W) S)) ≫ infinityAddition W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityFiniteAddition W b := by
  let f : InfinityAdditionRing W →ₐ[R] S := IsScalarTower.toAlgHom R (InfinityAdditionRing W) S
  let z := algebraMap (InfinityAdditionRing W) S (infinityProjectiveDenominator W)
  let T := Localization.Away z
  let l : S →ₐ[R] T := IsScalarTower.toAlgHom R S T
  let p : ChartPairRing W true true →ₐ[R] T :=
    (l.comp f).comp ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W))
  let k : ProjectiveAdditionRing W true true true →ₐ[R] T :=
    IsLocalization.Away.liftAlgHom (projectiveAdditionDenominator W true true true) (f := p)
      (isUnit_iff_exists_inv.mpr ⟨IsLocalization.Away.invSelf z,
        IsLocalization.Away.mul_invSelf (S := T) z⟩)
  have hk : k.comp (projectiveAdditionRestriction W true true true) = p := by
    apply AlgHom.ext
    intro x
    simp [k, projectiveAdditionRestriction]
  have hp : p = (l.comp g).comp (infinityFiniteRestriction W b) := by
    exact congrArg (fun q : ChartPairRing W true true →ₐ[R] S ↦ l.comp q) h
  have hn (i : Fin 3) :
      chartPointCoords W true (k.comp (projectiveAdditionSum W true true true)) i =
        (l.comp g) (infinityFiniteRestriction W b (chartPairSum W true true i)) *
          k (projectiveAdditionInv W true true true) := by
    rw [projectiveAdditionSum_normalized_map]
    exact congrArg (· * k (projectiveAdditionInv W true true true))
      (DFunLike.congr_fun (hk.trans hp) (chartPairSum W true true i))
  have hfinite := infinityFiniteAddition_normalized W b true (l.comp g)
    (k.comp (projectiveAdditionSum W true true true))
    (k (projectiveAdditionInv W true true true)) hn
  have hinfinity := infinity_projective_addition_agreement W true (l.comp f) k hk.symm
  have hdense :
      Spec.map (CommRingCat.ofHom (l.comp f).toRingHom) ≫ infinityAddition W =
        Spec.map (CommRingCat.ofHom (l.comp g).toRingHom) ≫ infinityFiniteAddition W b := by
    unfold infinityAddition
    rw [← Category.assoc, ← Spec.map_comp]
    exact hinfinity.trans hfinite.symm
  let j := Spec.map (CommRingCat.ofHom (algebraMap S T))
  have : IsSchemeTheoreticallyDominant j := infinityProjective_flat_schematic_dominance W
  refine hom_ext_of_schematic_dominance (toBase W) ?_ j ?_
  · rw [Category.assoc, Category.assoc, infinityAddition_toBase,
      infinityFiniteAddition_toBase, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (f.comp_algebraMap).trans g.comp_algebraMap.symm
  · change j ≫ (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityAddition W) =
      j ≫ (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityFiniteAddition W b)
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    exact hdense


/-- The two remaining comparisons on the actual intersections of the infinity cover. -/
theorem infinityFiniteAddition_origin_pullback [W.IsElliptic] (b : Bool) :
    pullback.fst
      (Spec.map (CommRingCat.ofHom
        ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityFiniteRestriction W b).toRingHom)) ≫
        infinityAddition W =
      pullback.snd _ _ ≫ infinityFiniteAddition W b := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true true) (InfinityAdditionRing W))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true true) (InfinityFiniteRing W b)))) ≫ infinityAddition W =
      pullback.snd _ _ ≫ infinityFiniteAddition W b
  apply (cancel_epi (pullbackSpecIso (ChartPairRing W true true)
    (InfinityAdditionRing W) (InfinityFiniteRing W b)).inv).mp
  simp only [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  let D := InfinityAdditionRing W ⊗[ChartPairRing W true true] InfinityFiniteRing W b
  let r : InfinityFiniteRing W b →ₐ[R] D :=
    (Algebra.TensorProduct.includeRight :
      InfinityFiniteRing W b →ₐ[ChartPairRing W true true] D).restrictScalars R
  have hi : (IsScalarTower.toAlgHom R (InfinityAdditionRing W) D).comp
      ((infinityAdditionRestriction W).comp (infinitySlopeRestriction W)) =
      r.comp (infinityFiniteRestriction W b) := by
    apply AlgHom.ext
    intro x
    have hl := (Algebra.TensorProduct.includeLeft :
      InfinityAdditionRing W →ₐ[ChartPairRing W true true] D).commutes x
    have hr := (Algebra.TensorProduct.includeRight :
      InfinityFiniteRing W b →ₐ[ChartPairRing W true true] D).commutes x
    exact hl.trans hr.symm
  exact infinityFinite_addition_agreement_of_flat W b r hi

end WeierstrassCurve.CubicCharts
