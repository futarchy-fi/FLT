/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeAffineCharts
public import FLT.Mazur.OneGonNormalizationPullback

/-!
# The one-gon node chart and the actual projective torus

The affine normalization coordinate t sends 0 to projective zero and 1 to
projective infinity. Its puncture maps to the torus by z=t/(t-1). Transporting
the gluing square to the specified cocone keeps this coordinate change.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation OneGonTransition
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)

/-- The full projective torus agrees with the torus used in the one-gon gluing. -/
lemma one_torus_eq (i : Fin 1) :
    (torusToComponent K ≫ componentι K 1 i ≫ p).left =
      OneGonGluing.torus K ≫ (polygonIso K 1 hn p q h).hom.left := by
  conv_lhs => rw [← normalization_polygonIso K 1 hn p q h]
  change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
    (componentι K 1 i ≫ OneGonNormalization.normalizationOver K).left ≫ _ = _
  rw [OneGonNormalization.componentι_normalizationOver]
  change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
    OneGonNormalization.normalization K ≫ _ = _
  rw [← Category.assoc, OneGonNormalization.torus_normalization]

/-- The B-chart normalization is the specified projective component map. -/
@[reassoc]
lemma oneBranch_oneChart (i : Fin 1) :
    PinchingAffineDescent.oneBranch K ≫ oneChart K hn p q h =
      OneGonAffineNormalization.alpha K ≫ (componentι K 1 i ≫ p).left := by
  conv_rhs => rw [← normalization_polygonIso K 1 hn p q h]
  change PinchingAffineDescent.oneBranch K ≫ _ =
    OneGonAffineNormalization.alpha K ≫
      (componentι K 1 i ≫ OneGonNormalization.normalizationOver K).left ≫ _
  rw [OneGonNormalization.componentι_normalizationOver]
  change _ = OneGonAffineNormalization.alpha K ≫ OneGonNormalization.normalization K ≫ _
  rw [← Category.assoc, OneGonAffineNormalization.alpha_normalization, Category.assoc]
  rfl

/-- Endpoint zero in the B normalization is projective zero. -/
lemma one_normalization_zero : ProjectiveLine.chartZero K ≫ OneGonAffineNormalization.alpha K =
    ProjectiveLine.zero K := OneGonAffineNormalization.zero_alpha K

/-- Endpoint one in the B normalization is projective infinity. -/
lemma one_normalization_one : PinchingAffineDescent.chartOne K ≫
    OneGonAffineNormalization.alpha K = ProjectiveLine.infinity K :=
  OneGonAffineNormalization.one_alpha K

/-- The actual puncture retains the Möbius change to the projective torus coordinate. -/
@[reassoc]
lemma one_puncture_torus (i : Fin 1) :
    bPuncture K ≫ oneChart K hn p q h =
      toTorus K ≫ (torusToComponent K ≫ componentι K 1 i ≫ p).left := by
  rw [one_torus_eq, oneChart, ← Category.assoc, OneGonGluing.overlap_condition,
    Category.assoc]

/-- The unrefined node and torus meet exactly on the punctured normalization. -/
lemma one_torus_isPullback (i : Fin 1) :
    IsPullback (bPuncture K) (toTorus K) (oneChart K hn p q h)
      (torusToComponent K ≫ componentι K 1 i ≫ p).left := by
  let := torus_isOpenImmersion K 1 hn p q h i
  apply IsOpenImmersion.isPullback _ _ _ _ (one_puncture_torus K hn p q h i).symm
  ext t
  change (torusToComponent K ≫ componentι K 1 i ≫ p).left t ∈
    Set.range (oneChart K hn p q h) ↔ t ∈ Set.range (toTorus K)
  constructor
  · rintro ⟨z, hz⟩
    rw [one_torus_eq K hn p q h i] at hz
    have he : OneGonGluing.node K z = OneGonGluing.torus K t :=
      (polygonIso K 1 hn p q h).hom.left.homeomorph.injective hz
    obtain ⟨s, _, hs⟩ := OneGonNormalizationPullback.intersection K z t he
    exact ⟨s, hs⟩
  · rintro ⟨s, rfl⟩
    exact ⟨bPuncture K s, congrArg (fun f ↦ f s) (one_puncture_torus K hn p q h i)⟩

end FLT.Mazur.PolygonNodeAffineCharts
