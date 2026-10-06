/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityPieces
public import FLT.EllipticCurve.CubicMixedRestriction

/-! # Agreement of the two finite-input pieces of the infinity-chart cover -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem infinityFiniteOverlap_input (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S] (f : InfinityFiniteRing W b →ₐ[R] S) :
    (f.comp (infinityFiniteOverlap W b)).comp
        (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)) =
      f.comp (infinityFiniteInput W b b) := by
  apply AlgHom.ext
  intro x
  exact congrArg f (infinityFiniteOverlap_restriction W b x)

/-- The two finite-input constructions agree on every common domain over the
infinity-chart product, including nonreduced coefficient rings. -/
theorem infinityFinite_addition_agreement [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (f : InfinityFiniteRing W false →ₐ[R] S)
    (g : InfinityFiniteRing W true →ₐ[R] S)
    (h : f.comp (infinityFiniteRestriction W false) =
      g.comp (infinityFiniteRestriction W true)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityFiniteAddition W false =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityFiniteAddition W true := by
  have hi (b : Bool) : f.comp (infinityFiniteInput W false b) =
      g.comp (infinityFiniteInput W true b) := by
    exact congrArg (fun k : ChartPairRing W true true →ₐ[R] S ↦
      k.comp (infinityPairInput W b)) h
  let a := f.comp (infinityFiniteAffine W false)
  let b := g.comp (infinityFiniteAffine W true)
  have hright : f.comp (infinityFiniteInput W false true) =
      (g.comp (infinityFiniteOverlap W true)).comp
        (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)) :=
    (hi true).trans (infinityFiniteOverlap_input W true g).symm
  have hleft : g.comp (infinityFiniteInput W true false) =
      (f.comp (infinityFiniteOverlap W false)).comp
        (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)) :=
    (hi false).symm.trans (infinityFiniteOverlap_input W false f).symm
  have hl : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityFiniteAddition W false =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
        affineAddition W := by
    have he : f.comp (infinityFinitePair W false) =
        Algebra.TensorProduct.productMap a
          ((g.comp (infinityFiniteOverlap W true)).comp
            (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) := by
      apply Algebra.TensorProduct.ext'
      intro x y
      change f (infinityFiniteAffine W false x * infinityFiniteInput W false true y) = _
      rw [map_mul]
      exact congrArg (a x * ·) (DFunLike.congr_fun hright y)
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (infinityFinitePair W false).toRingHom) ≫
        oppositeMixedAddition W) = _
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (f.comp (infinityFinitePair W false)).toRingHom) ≫ oppositeMixedAddition W = _
    rw [he]
    exact oppositeMixedAddition_on_overlap W a (g.comp (infinityFiniteOverlap W true))
  have hr : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityFiniteAddition W true =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
        affineAddition W := by
    have he : g.comp (infinityFinitePair W true) =
        Algebra.TensorProduct.productMap
          ((f.comp (infinityFiniteOverlap W false)).comp
            (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) b := by
      apply Algebra.TensorProduct.ext'
      intro x y
      change g (infinityFiniteInput W true false x * infinityFiniteAffine W true y) = _
      rw [map_mul]
      exact congrArg (· * b y) (DFunLike.congr_fun hleft x)
    change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (infinityFinitePair W true).toRingHom) ≫
        mixedChartAddition W) = _
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (g.comp (infinityFinitePair W true)).toRingHom) ≫ mixedChartAddition W = _
    rw [he]
    exact mixedChartAddition_on_overlap W (f.comp (infinityFiniteOverlap W false)) b
  exact hl.trans hr.symm


/-- Agreement on the actual scheme-theoretic intersection used by descent. -/
theorem infinityFiniteAddition_pullback [W.IsElliptic] :
    pullback.fst
      (Spec.map (CommRingCat.ofHom (infinityFiniteRestriction W false).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityFiniteRestriction W true).toRingHom)) ≫
        infinityFiniteAddition W false =
      pullback.snd _ _ ≫ infinityFiniteAddition W true := by
  change pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true true) (InfinityFiniteRing W false))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartPairRing W true true) (InfinityFiniteRing W true)))) ≫
        infinityFiniteAddition W false =
      pullback.snd _ _ ≫ infinityFiniteAddition W true
  apply (cancel_epi (pullbackSpecIso (ChartPairRing W true true)
    (InfinityFiniteRing W false) (InfinityFiniteRing W true)).inv).mp
  simp only [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  let D := InfinityFiniteRing W false ⊗[ChartPairRing W true true] InfinityFiniteRing W true
  let l : InfinityFiniteRing W false →ₐ[R] D :=
    (Algebra.TensorProduct.includeLeft :
      InfinityFiniteRing W false →ₐ[ChartPairRing W true true] D).restrictScalars R
  let r : InfinityFiniteRing W true →ₐ[R] D :=
    (Algebra.TensorProduct.includeRight :
      InfinityFiniteRing W true →ₐ[ChartPairRing W true true] D).restrictScalars R
  have hi : l.comp (infinityFiniteRestriction W false) =
      r.comp (infinityFiniteRestriction W true) := by
    apply AlgHom.ext
    intro x
    have hl := (Algebra.TensorProduct.includeLeft :
      InfinityFiniteRing W false →ₐ[ChartPairRing W true true] D).commutes x
    have hr := (Algebra.TensorProduct.includeRight :
      InfinityFiniteRing W true →ₐ[ChartPairRing W true true] D).commutes x
    exact hl.trans hr.symm
  exact infinityFinite_addition_agreement W l r hi

end WeierstrassCurve.CubicCharts
