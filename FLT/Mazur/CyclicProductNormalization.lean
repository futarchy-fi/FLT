/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeNormalizationBaseChange
public import FLT.Mazur.PolygonCyclicNormalizationPullback
public import FLT.Mazur.PolygonProductAtlas
/-!
# Cyclic normalization charts after affine base change

The product-polynomial normalization chart is cartesian over each node of the
actual pulled-back cyclic polygon. The coproduct comparison is explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
universe u
namespace FLT.Mazur.CyclicProductNormalization
open PinchingChartBaseChange PolygonCyclicNormalizationPullback
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
variable (n : ℕ) (hn : 2 ≤ n)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The structure morphism of the normalization coproduct. -/
def componentsBase : components K n ⟶ Spec (.of K) :=
  Sigma.desc fun _ ↦ ProjectiveLine.toBase K

@[reassoc (attr := simp)] theorem normalization_toBase :
    normalization K n hn ≫ PolygonCyclicAtlas.toBase K n hn = componentsBase K n := by
  apply Sigma.hom_ext
  intro i
  simp [normalization, componentsBase]

/-- The two affine branches mapped into adjacent normalization components. -/
def affineLift (j : Fin n) : Spec (.of (K[X] × K[X])) ⟶ components K n :=
  inv (coprodSpec K[X] K[X]) ≫ chartLift K n hn j

@[reassoc] theorem coprodSpec_normalization :
    coprodSpec K[X] K[X] ≫ NodeNormalizationBaseChange.normalization K =
      affineNormalization K := by
  apply coprod.hom_ext
  · rw [coprodSpec_inl_assoc, affineNormalization, coprod.inl_desc]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · rw [coprodSpec_inr_assoc, affineNormalization, coprod.inr_desc]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl

@[reassoc] theorem affineLift_normalization (j : Fin n) :
    affineLift K n hn j ≫ normalization K n hn =
      NodeNormalizationBaseChange.normalization K ≫ PolygonCyclicAtlas.chart K n hn j := by
  rw [affineLift, Category.assoc, chartLift_normalization,
    ← coprodSpec_normalization, Category.assoc, IsIso.inv_hom_id_assoc]

@[reassoc] theorem affineLift_toBase (j : Fin n) :
    affineLift K n hn j ≫ componentsBase K n =
      Spec.map (CommRingCat.ofHom (algebraMap K (K[X] × K[X]))) := by
  rw [← normalization_toBase K n hn, ← Category.assoc, affineLift_normalization,
    Category.assoc, PolygonCyclicAtlas.chart_toBase]
  exact NodeNormalizationBaseChange.normalization_base K

theorem affine_isPullback (j : Fin n) : IsPullback
    (NodeNormalizationBaseChange.normalization K) (affineLift K n hn j)
    (PolygonCyclicAtlas.chart K n hn j) (normalization K n hn) := by
  apply (PolygonCyclicNormalizationPullback.isPullback K n hn j).of_iso
    (asIso (coprodSpec K[X] K[X])) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [coprodSpec_normalization]
  · simp [affineLift]
  · simp
  · simp

/-- The actual parameter pullback of the normalization coproduct. -/
abbrev componentsProduct := pullback (parameter K S) (componentsBase K n)

/-- The global cyclic normalization after parameter base change. -/
def normalizationProduct : componentsProduct K S n ⟶
    PolygonProductAtlas.cyclicProduct K S n hn :=
  pullback.map _ _ _ _ (𝟙 _) (normalization K n hn) (𝟙 _) (by simp) (by simp)

/-- The product-polynomial chart in the pulled-back normalization. -/
def affineNormalizationLift (j : Fin n) :
    Spec (.of (S[X] × S[X])) ⟶ componentsProduct K S n :=
  (NodeNormalizationBaseChange.productIso K S).inv ≫
    pullback.map _ _ _ _ (𝟙 _) (affineLift K n hn j) (𝟙 _) (by simp)
      (by simpa using (affineLift_toBase K n hn j).symm)

@[reassoc (attr := simp)] theorem normalizationProduct_fst :
    normalizationProduct K S n hn ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [normalizationProduct]
@[reassoc (attr := simp)] theorem normalizationProduct_snd :
    normalizationProduct K S n hn ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ normalization K n hn := by simp [normalizationProduct]
@[reassoc (attr := simp)] theorem affineNormalizationLift_fst (j : Fin n) :
    affineNormalizationLift K S n hn j ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S[X] × S[X]))) := by
  simp [affineNormalizationLift]
@[reassoc (attr := simp)] theorem affineNormalizationLift_snd (j : Fin n) :
    affineNormalizationLift K S n hn j ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (NodeNormalizationBaseChange.coeff K S)) ≫
        affineLift K n hn j := by simp [affineNormalizationLift]

theorem affineNormalizationLift_normalization (j : Fin n) :
    NodeNormalizationBaseChange.normalization S ≫
      PolygonProductAtlas.cyclicChartMap K S n hn j =
        affineNormalizationLift K S n hn j ≫ normalizationProduct K S n hn := by
  apply pullback.hom_ext
  · simp only [Category.assoc, PolygonProductAtlas.cyclicChartMap_fst,
      normalizationProduct_fst, affineNormalizationLift_fst]
    exact NodeNormalizationBaseChange.normalization_base S
  · simp only [Category.assoc, PolygonProductAtlas.cyclicChartMap_snd,
      normalizationProduct_snd, affineNormalizationLift_snd_assoc]
    rw [← Category.assoc, NodeNormalizationBaseChange.normalization_coeff,
      Category.assoc, affineLift_normalization]

theorem normalizationProduct_isPullback : IsPullback (normalizationProduct K S n hn)
    (pullback.snd _ _) (pullback.snd _ _) (normalization K n hn) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _)
    (h₂₂ := PolygonCyclicAtlas.toBase K n hn)
  · simpa only [normalizationProduct_fst, normalization_toBase] using
      (IsPullback.of_hasPullback (parameter K S) (componentsBase K n))
  · exact normalizationProduct_snd K S n hn
  · exact IsPullback.of_hasPullback _ _

theorem node_isPullback (j : Fin n) : IsPullback
    (NodeNormalizationBaseChange.normalization S) (affineNormalizationLift K S n hn j)
    (PolygonProductAtlas.cyclicChartMap K S n hn j) (normalizationProduct K S n hn) := by
  apply IsPullback.of_bot _ (affineNormalizationLift_normalization K S n hn j)
    (normalizationProduct_isPullback K S n hn)
  simpa only [affineNormalizationLift_snd, PolygonProductAtlas.cyclicChartMap_snd] using
    (NodeNormalizationBaseChange.coefficient_isPullback K S).paste_vert
      (affine_isPullback K n hn j)
end FLT.Mazur.CyclicProductNormalization
