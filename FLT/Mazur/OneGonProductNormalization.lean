/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProductAtlas
public import FLT.Mazur.OneGonNormalizationPullback
public import FLT.Mazur.OneGonCocone
public import FLT.Mazur.ProjectiveLineProductCharts
/-!
# The one-gon normalization after affine base change

Polynomial and equalizer coordinates identify the normalization square in the
actual pulled-back one-gon. No flatness assumption is needed for this comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.OneGonProductNormalization
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
open PinchingChartBaseChange ProjectiveLineProductCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem alpha_toBase : OneGonAffineNormalization.alpha K ≫ ProjectiveLine.toBase K =
    ProjectiveLine.chartToBase K := by
  rw [← OneGonNormalization.normalization_toBase K, ← Category.assoc,
    OneGonAffineNormalization.alpha_normalization, Category.assoc, OneGonGluing.node_toBase]
  rw [PinchingAffineDescent.oneBranch, PolygonNodePresentation.bToBase,
    ProjectiveLine.chartToBase, ← Spec.map_comp]
  rfl

/-- The normalization morphism after affine parameter base change. -/
def normalizationProduct : product K S ⟶
    PolygonProductAtlas.oneGonProduct K S :=
  pullback.map _ _ _ _ (𝟙 _) (OneGonNormalization.normalization K) (𝟙 _)
    (by simp [parameterToBase, parameter]) (by simp)

/-- The affine normalization chart in the pulled-back projective line. -/
def affineNormalizationLift : Spec (.of (Polynomial S)) ⟶ product K S :=
  (chartProductIso K S).inv ≫
    pullback.map _ _ _ _ (𝟙 _) (OneGonAffineNormalization.alpha K) (𝟙 _)
      (by simp) (by simpa using (alpha_toBase K).symm)

@[reassoc (attr := simp)] theorem normalizationProduct_fst :
    normalizationProduct K S ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [normalizationProduct]
@[reassoc (attr := simp)] theorem normalizationProduct_snd :
    normalizationProduct K S ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ OneGonNormalization.normalization K := by
  simp [normalizationProduct]
@[reassoc (attr := simp)] theorem affineNormalizationLift_fst :
    affineNormalizationLift K S ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) := by
  simp [affineNormalizationLift]
@[reassoc (attr := simp)] theorem affineNormalizationLift_snd :
    affineNormalizationLift K S ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) ≫
        OneGonAffineNormalization.alpha K := by
  simp [affineNormalizationLift]

theorem normalization_coeff :
    Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (OneGonScalarExtension.coeffMap (R := K) (S := S)).toRingHom) =
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) ≫
      PinchingAffineDescent.oneBranch K := by
  rw [PinchingAffineDescent.oneBranch, ← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem normalization_base :
    Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom) ≫
      oneGonBase S = Spec.map (CommRingCat.ofHom (algebraMap S (Polynomial S))) := by
  rw [oneGonBase, ← Spec.map_comp]
  rfl

theorem affineNormalizationLift_normalization :
    Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom) ≫
      PolygonProductAtlas.oneGonChartMap K S false =
        affineNormalizationLift K S ≫ normalizationProduct K S := by
  apply pullback.hom_ext
  · simp only [Category.assoc, PolygonProductAtlas.oneGonNode_fst,
      normalizationProduct_fst, affineNormalizationLift_fst]
    exact normalization_base S
  · simp only [Category.assoc, PolygonProductAtlas.oneGonNode_snd,
      normalizationProduct_snd, affineNormalizationLift_snd_assoc]
    rw [← Category.assoc, normalization_coeff, Category.assoc,
      OneGonAffineNormalization.alpha_normalization]

theorem normalizationProduct_isPullback :
    IsPullback (normalizationProduct K S) (pullback.snd _ _)
      (pullback.snd _ _) (OneGonNormalization.normalization K) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := OneGonGluing.toBase K)
  · simpa only [normalizationProduct_fst, OneGonNormalization.normalization_toBase] using
      (IsPullback.of_hasPullback (parameterToBase K S) (ProjectiveLine.toBase K))
  · exact normalizationProduct_snd K S
  · exact IsPullback.of_hasPullback _ _

theorem coefficient_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))))
      (Spec.map (CommRingCat.ofHom (OneGonScalarExtension.coeffMap (R := K) (S := S)).toRingHom))
      (PinchingAffineDescent.oneBranch K) := by
  have hB : IsPullback (oneGonBase S)
      (Spec.map (CommRingCat.ofHom (OneGonScalarExtension.coeffMap (R := K) (S := S)).toRingHom))
      (parameter K S) (oneGonBase K) := by
    exact IsPullback.of_iso_pullback ⟨by
      rw [← oneGonProductIso_inv_fst K S, ← oneGonProductIso_inv_snd K S]
      simp only [Category.assoc, pullback.condition]⟩ (oneGonProductIso K S).symm
        (oneGonProductIso_inv_fst K S) (oneGonProductIso_inv_snd K S)
  apply IsPullback.of_right (h₁₂ := oneGonBase S) (h₂₂ := oneGonBase K) _
    (normalization_coeff K S) hB
  rw [normalization_base]
  have hb : PinchingAffineDescent.oneBranch K ≫ oneGonBase K =
      ProjectiveLine.chartToBase K := by
    rw [PinchingAffineDescent.oneBranch, normalization_base]
    rfl
  rw [hb]
  exact IsPullback.of_iso_pullback ⟨by
    rw [← chartProductIso_inv_fst K S, ← chartProductIso_inv_snd K S]
    change (chartProductIso K S).inv ≫ pullback.fst _ _ ≫ parameterToBase K S = _
    rw [pullback.condition, Category.assoc]⟩ (chartProductIso K S).symm
      (chartProductIso_inv_fst K S) (chartProductIso_inv_snd K S)

theorem node_isPullback : IsPullback
    (Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom))
    (affineNormalizationLift K S) (PolygonProductAtlas.oneGonChartMap K S false)
    (normalizationProduct K S) := by
  apply IsPullback.of_bot _ (affineNormalizationLift_normalization K S)
    (normalizationProduct_isPullback K S)
  simpa only [affineNormalizationLift_snd, PolygonProductAtlas.oneGonNode_snd] using
    (coefficient_isPullback K S).paste_vert (OneGonNormalizationPullback.node_isPullback K)
end FLT.Mazur.OneGonProductNormalization
