/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonProductNormalization
/-!
# The torus chart of the base-changed one-gon normalization

The full torus chart pulls back identically along normalization, in the
canonical tensor coordinates used by the product atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped LaurentPolynomial TensorProduct
universe u
namespace FLT.Mazur.OneGonProductTorus
open PinchingChartBaseChange OneGonProductNormalization OneGonNormalizationPullback
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem torusLift_toBase : torusLift K ≫ ProjectiveLine.toBase K =
    OneGonGluing.torusToBase K := by
  simp [torusLift]

/-- The full torus chart in the actual pulled-back projective normalization. -/
def torusNormalizationLift : Spec (.of (S ⊗[K] K[T;T⁻¹])) ⟶
    ProjectiveLineProductCharts.product K S :=
  (pullbackSpecIso K S K[T;T⁻¹]).inv ≫
    pullback.map _ _ _ _ (𝟙 _) (torusLift K) (𝟙 _)
      (by simp [ProjectiveLineProductCharts.parameterToBase])
      (by
        simp only [Category.comp_id]
        rw [torusLift_toBase, OneGonGluing.torusToBase]
        congr 1)

@[reassoc (attr := simp)] theorem torusNormalizationLift_fst :
    torusNormalizationLift K S ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[K] K[T;T⁻¹]))) := by
  simp [torusNormalizationLift]
  rfl
@[reassoc (attr := simp)] theorem torusNormalizationLift_snd :
    torusNormalizationLift K S ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K[T;T⁻¹] →ₐ[K] S ⊗[K] K[T;T⁻¹]).toRingHom) ≫
          torusLift K := by
  simp [torusNormalizationLift]

@[reassoc] theorem torusNormalizationLift_normalization :
    torusNormalizationLift K S ≫ normalizationProduct K S =
      PolygonProductAtlas.oneGonChartMap K S true := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, normalizationProduct_snd,
      torusNormalizationLift_snd_assoc, PolygonProductAtlas.oneGonTorus_snd]
    rw [← Category.assoc (ProjectiveLine.overlapLeft K),
      OneGonNormalization.torus_normalization]

theorem torus_isPullback : IsPullback (𝟙 (Spec (.of (S ⊗[K] K[T;T⁻¹]))))
    (torusNormalizationLift K S) (PolygonProductAtlas.oneGonChartMap K S true)
    (normalizationProduct K S) := by
  apply IsPullback.of_bot _ (by simp [torusNormalizationLift_normalization])
    (normalizationProduct_isPullback K S)
  simpa only [Category.id_comp, torusNormalizationLift_snd,
    PolygonProductAtlas.oneGonTorus_snd] using
    (IsPullback.of_id_fst (f := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : K[T;T⁻¹] →ₐ[K] S ⊗[K] K[T;T⁻¹]).toRingHom))).paste_vert
        (OneGonNormalizationPullback.torus_isPullback K)
end FLT.Mazur.OneGonProductTorus
