/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicGlobalAddition
public import FLT.EllipticCurve.CubicAffineInverse

/-! # Global identity and inverse laws for cubic addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The ordinary part of the infinity chart is schematically dense over any base ring. -/
instance infinityOverlap_schematic_dominance :
    IsSchemeTheoreticallyDominant (overlapInclusion W true) := by
  apply specMap_schematic_dominance
  change Function.Injective (algebraMap (Ring W true) (Overlap W true))
  apply IsLocalization.injective (Overlap W true)
    (M := Submonoid.powers (coord W true 1))
  apply Submonoid.powers_le.mpr
  simpa only [map_zero, sub_zero] using infinity_v_sub_mem_nonZeroDivisors W 0

/-- Equality on the ordinary chart determines maps into a separated relative target,
including over nonreduced coefficient rings. -/
theorem affineChart_hom_ext {Y B : Scheme.{u}} (s : Y ⟶ B) [IsSeparated s]
    {f g : scheme W ⟶ Y} (hbase : f ≫ s = g ≫ s)
    (h : affineChart W ≫ f = affineChart W ≫ g) : f = g := by
  apply (sourceOpenCover W).hom_ext
  intro b
  cases b
  · exact h
  · change infinityChart W ≫ f = infinityChart W ≫ g
    refine hom_ext_of_schematic_dominance s ?_ (overlapInclusion W true) ?_
    · simpa only [Category.assoc] using congrArg (fun k ↦ infinityChart W ≫ k) hbase
    · simpa only [← Category.assoc, changeChart_true_to_scheme] using
        congrArg (fun k ↦ Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) ≫ k) h

@[reassoc] theorem spec_productMap_left
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra R S] (a : A →ₐ[R] S) (b : B →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom) =
      Spec.map (CommRingCat.ofHom a.toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg (fun (f : A →ₐ[R] S) ↦ f.toRingHom)
    (Algebra.TensorProduct.productMap_left a b)

@[reassoc] theorem spec_productMap_right
    {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra R S] (a : A →ₐ[R] S) (b : B →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
      Spec.map (CommRingCat.ofHom b.toRingHom) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg (fun (f : B →ₐ[R] S) ↦ f.toRingHom)
    (Algebra.TensorProduct.productMap_right a b)

/-- A pair of chart-valued points as a point of the full cubic product. -/
def chartPairEvaluation (b c : Bool) {S : Type u} [CommRing S] [Algebra R S]
    (f : Ring W b →ₐ[R] S) (g : Ring W c →ₐ[R] S) :
    Spec (.of S) ⟶ pullback (toBase W) (toBase W) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap f g).toRingHom) ≫
    (pullbackSpecIso R (Ring W b) (Ring W c)).inv ≫ chartPairInclusion W b c

@[reassoc (attr := simp)] theorem chartPairEvaluation_fst (b c : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : Ring W b →ₐ[R] S) (g : Ring W c →ₐ[R] S) :
    chartPairEvaluation W b c f g ≫ pullback.fst (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ sourceChart W b := by
  simp only [chartPairEvaluation, chartPairInclusion, pullback.map, Category.assoc,
    pullback.lift_fst, chartToBase, pullbackSpecIso_inv_fst_assoc]
  exact spec_productMap_left_assoc f g (sourceChart W b)

@[reassoc (attr := simp)] theorem chartPairEvaluation_snd (b c : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : Ring W b →ₐ[R] S) (g : Ring W c →ₐ[R] S) :
    chartPairEvaluation W b c f g ≫ pullback.snd (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ sourceChart W c := by
  simp only [chartPairEvaluation, chartPairInclusion, pullback.map, Category.assoc,
    pullback.lift_snd, chartToBase, pullbackSpecIso_inv_snd_assoc]
  exact spec_productMap_right_assoc f g (sourceChart W c)

@[reassoc (attr := simp)] theorem chartPairEvaluation_addition [W.IsElliptic] (b c : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : Ring W b →ₐ[R] S) (g : Ring W c →ₐ[R] S) :
    chartPairEvaluation W b c f g ≫ addition W =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap f g).toRingHom) ≫
        chartAddition W b c := by
  simp [chartPairEvaluation, chartAdditionMorphism]

/-- The pair consisting of infinity and the variable point. -/
def leftIdentityPair : scheme W ⟶ pullback (toBase W) (toBase W) :=
  pullback.lift (toBase W ≫ infinity W) (𝟙 _) (by simp)

/-- The pair consisting of the variable point and infinity. -/
def rightIdentityPair : scheme W ⟶ pullback (toBase W) (toBase W) :=
  pullback.lift (𝟙 _) (toBase W ≫ infinity W) (by simp)

/-- The graph of the already constructed global negation. -/
def inverseGraph : scheme W ⟶ pullback (toBase W) (toBase W) :=
  pullback.lift (𝟙 _) (negation W) (by simp)

theorem affineChart_leftIdentityPair :
    affineChart W ≫ leftIdentityPair W =
      chartPairEvaluation W true false
        ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W)) (AlgHom.id R _) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, leftIdentityPair, pullback.lift_fst, chartPairEvaluation_fst]
    change affineChart W ≫ toBase W ≫ infinity W =
      Spec.map (CommRingCat.ofHom
        (((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W)).toRingHom)) ≫
          infinityChart W
    rw [← Category.assoc, affineChart_toBase]
    change Spec.map (CommRingCat.ofHom (algebraMap R (Ring W false))) ≫
      (Spec.map (CommRingCat.ofHom (InfinityChart.origin W).toRingHom) ≫ infinityChart W) = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  · simp only [Category.assoc, leftIdentityPair, pullback.lift_snd, Category.comp_id,
      chartPairEvaluation_snd]
    change affineChart W = Spec.map (𝟙 _) ≫ affineChart W
    simp

theorem affineChart_rightIdentityPair :
    affineChart W ≫ rightIdentityPair W =
      chartPairEvaluation W false true (AlgHom.id R _)
        ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rightIdentityPair, pullback.lift_fst, Category.comp_id,
      chartPairEvaluation_fst]
    change affineChart W = Spec.map (𝟙 _) ≫ affineChart W
    simp
  · simp only [Category.assoc, rightIdentityPair, pullback.lift_snd, chartPairEvaluation_snd]
    change affineChart W ≫ toBase W ≫ infinity W =
      Spec.map (CommRingCat.ofHom
        (((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W)).toRingHom)) ≫
          infinityChart W
    rw [← Category.assoc, affineChart_toBase]
    change Spec.map (CommRingCat.ofHom (algebraMap R (Ring W false))) ≫
      (Spec.map (CommRingCat.ofHom (InfinityChart.origin W).toRingHom) ≫ infinityChart W) = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

theorem affineChart_inverseGraph :
    affineChart W ≫ inverseGraph W =
      chartPairEvaluation W false false (AlgHom.id R _) (affineNegationEquiv W).toAlgHom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, inverseGraph, pullback.lift_fst, Category.comp_id,
      chartPairEvaluation_fst]
    change affineChart W = Spec.map (𝟙 _) ≫ affineChart W
    simp
  · simp only [Category.assoc, inverseGraph, pullback.lift_snd, chartPairEvaluation_snd,
      affineChart_negation]
    rfl

/-- Infinity is a left identity everywhere on the cubic, over arbitrary coefficient rings. -/
@[reassoc (attr := simp)] theorem addition_zero_left [W.IsElliptic] :
    leftIdentityPair W ≫ addition W = 𝟙 (scheme W) := by
  apply affineChart_hom_ext W (toBase W)
  · simp [leftIdentityPair]
  · rw [← Category.assoc, affineChart_leftIdentityPair, chartPairEvaluation_addition]
    exact mixedChartAddition_zero W

/-- Infinity is a right identity everywhere on the cubic. -/
@[reassoc (attr := simp)] theorem addition_zero_right [W.IsElliptic] :
    rightIdentityPair W ≫ addition W = 𝟙 (scheme W) := by
  apply affineChart_hom_ext W (toBase W)
  · simp [rightIdentityPair]
  · rw [← Category.assoc, affineChart_rightIdentityPair, chartPairEvaluation_addition]
    exact oppositeMixedAddition_zero W

/-- The global negation is a right inverse for addition on the whole cubic. -/
@[reassoc (attr := simp)] theorem addition_inverse_right [W.IsElliptic] :
    inverseGraph W ≫ addition W = toBase W ≫ infinity W := by
  apply affineChart_hom_ext W (toBase W)
  · simp [inverseGraph]
  · rw [← Category.assoc, affineChart_inverseGraph, chartPairEvaluation_addition]
    simpa only [← Category.assoc, affineChart_toBase, chartAddition, inversePair] using
      affineAddition_inverse W

end WeierstrassCurve.CubicCharts
