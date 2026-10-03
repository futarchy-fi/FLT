/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonProductNormalization
public import FLT.Mazur.RelativePinchingDescent
/-!
# Endpoints in the base-changed one-gon normalization

Zero and one in the affine normalization map to the actual pulled-back zero
and infinity sections. Their equality supplies the relative pinching descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.OneGonProductEndpoints
open OneGonProductNormalization PinchingChartBaseChange ProjectiveLineProductCharts
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual constant endpoint section after parameter base change. -/
def endpoint (b : Bool) : Spec (.of S) ⟶ product K S :=
  pullback.lift (𝟙 _) (parameter K S ≫
    (if b then ProjectiveLine.infinity K else ProjectiveLine.zero K)) (by
      cases b <;> simp [parameter, parameterToBase])

@[reassoc (attr := simp)] theorem endpoint_fst (b : Bool) :
    endpoint K S b ≫ pullback.fst _ _ = 𝟙 _ := by simp [endpoint]
@[reassoc (attr := simp)] theorem endpoint_snd (b : Bool) :
    endpoint K S b ≫ pullback.snd _ _ = parameter K S ≫
      (if b then ProjectiveLine.infinity K else ProjectiveLine.zero K) := by simp [endpoint]

theorem eval_coeff (b : Bool) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (if b then (1 : S) else 0))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) =
    parameter K S ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (if b then (1 : K) else 0))) := by
  rw [parameter, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext <;> cases b <;> simp

@[reassoc] theorem eval_affineNormalizationLift (b : Bool) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (if b then (1 : S) else 0))) ≫
      affineNormalizationLift K S = endpoint K S b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, affineNormalizationLift_fst, endpoint_fst,
      ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext
    simp
  · rw [Category.assoc, affineNormalizationLift_snd, endpoint_snd, ← Category.assoc,
      eval_coeff, Category.assoc]
    cases b
    · exact congrArg (parameter K S ≫ ·) (OneGonAffineNormalization.zero_alpha K)
    · exact congrArg (parameter K S ≫ ·) (OneGonAffineNormalization.one_alpha K)

/-- The node section in the equalizer chart of the pulled-back one-gon. -/
def nodeSection : Spec (.of S) ⟶ PolygonProductAtlas.oneGonProduct K S :=
  Spec.map (CommRingCat.ofHom (PolygonNodePresentation.bEval (R := S)).toRingHom) ≫
    PolygonProductAtlas.oneGonChartMap K S false

@[reassoc] theorem endpoint_normalization (b : Bool) :
    endpoint K S b ≫ normalizationProduct K S = nodeSection K S := by
  rw [← eval_affineNormalizationLift, Category.assoc,
    ← affineNormalizationLift_normalization, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  cases b
  · rfl
  · exact ((PolygonNodePresentation.mem_B _).mp p.property).symm

include K in
theorem endpoint_relation {Y : Scheme.{u}} (h : product K S ⟶ Y)
    (w : endpoint K S false ≫ h = endpoint K S true ≫ h) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)) ≫
      affineNormalizationLift K S ≫ h =
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 1)) ≫
      affineNormalizationLift K S ≫ h := by
  have h0 := eval_affineNormalizationLift K S false
  have h1 := eval_affineNormalizationLift K S true
  simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
  rw [← Category.assoc, ← Category.assoc, h0, h1]
  exact w

theorem node_desc {Y : Scheme.{u}} (h : product K S ⟶ Y)
    (w : endpoint K S false ≫ h = endpoint K S true ≫ h) :
    ∃! d : Spec (.of (PolygonNodePresentation.B (R := S))) ⟶ Y,
      Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom) ≫ d =
        affineNormalizationLift K S ≫ h :=
  RelativePinchingDescent.oneGon_desc _ (endpoint_relation K S h w)
end FLT.Mazur.OneGonProductEndpoints
