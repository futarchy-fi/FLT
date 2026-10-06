/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityRestriction
public import FLT.EllipticCurve.CubicChartProductCover

/-! # The four chart additions and their input transition identities -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The verified addition on each of the four products of input charts. -/
def chartAddition [W.IsElliptic] :
    ∀ b c, Spec (.of (ChartPairRing W b c)) ⟶ scheme W
  | false, false => affineAddition W
  | false, true => oppositeMixedAddition W
  | true, false => mixedChartAddition W
  | true, true => infinityChartAddition W

@[reassoc (attr := simp)] theorem chartAddition_toBase [W.IsElliptic] (b c : Bool) :
    chartAddition W b c ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartPairRing W b c))) := by
  cases b <;> cases c
  · exact affineAddition_toBase W
  · exact oppositeMixedAddition_toBase W
  · exact mixedChartAddition_toBase W
  · exact infinityChartAddition_toBase W

/-- The same chart addition on the categorical product. -/
def chartAdditionMorphism [W.IsElliptic] (b c : Bool) :
    pullback (chartToBase W b) (chartToBase W c) ⟶ scheme W :=
  (pullbackSpecIso R (Ring W b) (Ring W c)).hom ≫ chartAddition W b c

@[reassoc (attr := simp)] theorem chartAdditionMorphism_toBase [W.IsElliptic] (b c : Bool) :
    chartAdditionMorphism W b c ≫ toBase W =
      pullback.fst (chartToBase W b) (chartToBase W c) ≫ chartToBase W b := by
  rw [chartAdditionMorphism, Category.assoc, chartAddition_toBase]
  exact pullbackSpecIso_hom_base R (Ring W b) (Ring W c)

theorem chartAddition_change_first [W.IsElliptic] (c : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (a : Overlap W true →ₐ[R] S) (v : Ring W c →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
      (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) v).toRingHom) ≫
        chartAddition W true c =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.productMap (a.comp (changeChart W true)) v).toRingHom) ≫
          chartAddition W false c := by
  cases c
  · exact mixedChartAddition_on_overlap W a v
  · exact infinityChartAddition_on_first_overlap W a v

theorem chartAddition_change_second [W.IsElliptic] (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (v : Ring W b →ₐ[R] S) (a : Overlap W true →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap v
      (a.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)))).toRingHom) ≫
        chartAddition W b true =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.productMap v (a.comp (changeChart W true))).toRingHom) ≫
          chartAddition W b false := by
  cases b
  · exact oppositeMixedAddition_on_overlap W v a
  · exact infinityChartAddition_on_second_overlap W v a

/-- Naturality of the spectrum tensor-product comparison, with explicit algebra maps. -/
theorem pullbackSpecIso_productMap
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (a : A →ₐ[R] B) (b : C →ₐ[R] D) :
    (pullbackSpecIso R B D).inv ≫
      pullback.map
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R D)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R C)))
        (Spec.map (CommRingCat.ofHom a.toRingHom))
        (Spec.map (CommRingCat.ofHom b.toRingHom)) (𝟙 _)
        (by
          rw [← Spec.map_comp]
          simp only [Category.comp_id]
          exact congrArg
            (fun (f : R →+* B) ↦ Spec.map (CommRingCat.ofHom f)) a.comp_algebraMap.symm)
        (by
          rw [← Spec.map_comp]
          simp only [Category.comp_id]
          exact congrArg
            (fun (f : R →+* D) ↦ Spec.map (CommRingCat.ofHom f)) b.comp_algebraMap.symm) ≫
      (pullbackSpecIso R A C).hom =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap
          ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] D).comp a)
          ((Algebra.TensorProduct.includeRight : D →ₐ[R] B ⊗[R] D).comp b)).toRingHom) := by
  apply (cancel_mono (pullbackSpecIso R A C).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc,
      pullbackSpecIso_inv_fst]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (congrArg (fun (f : A →ₐ[R] B ⊗[R] D) ↦ f.toRingHom)
      (Algebra.TensorProduct.productMap_left
        ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] D).comp a)
        ((Algebra.TensorProduct.includeRight : D →ₐ[R] B ⊗[R] D).comp b))).symm
  · simp only [Category.assoc, pullback.map, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc,
      pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (congrArg (fun (f : C →ₐ[R] B ⊗[R] D) ↦ f.toRingHom)
      (Algebra.TensorProduct.productMap_right
        ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] D).comp a)
        ((Algebra.TensorProduct.includeRight : D →ₐ[R] B ⊗[R] D).comp b))).symm

end WeierstrassCurve.CubicCharts
