/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNormalization
public import FLT.Mazur.PolygonPinchingDiagram

/-!
# The specified one-gon pinching cocone

The normalization and node morphisms preserve the base field and form a
cocone on the specified one-component cyclic pinching diagram. No closed
pinching universal property is assumed or asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace FLT.Mazur.OneGonNormalization

open OneGonAffineCover OneGonNormalizationCoordinates PolygonNodePresentation

variable (K : Type u) [Field K]

/-- Every local normalization coordinate preserves the coefficient field. -/
theorem patch_toBase (c : awayOne K) :
    Spec.map (CommRingCat.ofHom ((aeval c).toRingHom.comp (B (R := K)).val.toRingHom)) ≫
      bToBase K = openOne K ≫ ProjectiveLine.chartToBase K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (aeval c).commutes r

@[reassoc (attr := simp)]
theorem leftPatch_toBase : leftPatch K ≫ bToBase K =
    openOne K ≫ ProjectiveLine.chartToBase K := patch_toBase K _

@[reassoc (attr := simp)]
theorem rightPatch_toBase : rightPatch K ≫ bToBase K =
    openOne K ≫ ProjectiveLine.chartToBase K := patch_toBase K _

@[reassoc (attr := simp)]
theorem overlapLeft_toBase : ProjectiveLine.overlapLeft K ≫ ProjectiveLine.chartToBase K =
    OneGonGluing.torusToBase K := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext Polynomial.toLaurent_C

@[reassoc]
theorem inversion_toBase :
    (ProjectiveLine.inversion K).hom ≫ OneGonGluing.torusToBase K =
      OneGonGluing.torusToBase K := by
  rw [ProjectiveLine.inversion_hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext LaurentPolynomial.invert_C

@[reassoc (attr := simp)]
theorem leftMap_toBase : leftMap K ≫ OneGonGluing.toBase K = ProjectiveLine.chartToBase K := by
  apply (isPushout K).hom_ext <;> simp

@[reassoc (attr := simp)]
theorem rightMap_toBase : rightMap K ≫ OneGonGluing.toBase K = ProjectiveLine.chartToBase K := by
  apply (isPushout K).hom_ext
  · simpa only [overlapLeft_rightMap_assoc, OneGonGluing.torus_toBase, overlapLeft_toBase]
      using inversion_toBase K
  · simp

@[reassoc (attr := simp)]
theorem normalization_toBase : normalization K ≫ OneGonGluing.toBase K =
    ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ _ = ProjectiveLine.left K ≫ _
    simp
  · change ProjectiveLine.right K ≫ _ = ProjectiveLine.right K ≫ _
    simp

/-- The normalization restricts to the entire Laurent chart, including coordinate one. -/
@[reassoc]
theorem torus_normalization :
    (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ normalization K =
      OneGonGluing.torus K := by simp

@[reassoc (attr := simp)]
theorem origin_toBase : bOrigin K ≫ bToBase K = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r
  exact (bEval (R := K)).commutes r

/-- The one-gon as a scheme over the coefficient field. -/
def polygon : Over (Spec (.of K)) := Over.mk (OneGonGluing.toBase K)

/-- Normalization from the specified coproduct with one component. -/
def normalizationOver : PolygonPinching.components K 1 ⟶ polygon K :=
  Sigma.desc fun _ ↦ Over.homMk (normalization K) (normalization_toBase K)

/-- The specified node is the origin of the actual equalizer chart. -/
def nodes : PolygonPinching.nodes K 1 ⟶ polygon K :=
  Sigma.desc fun _ ↦ Over.homMk (bOrigin K ≫ OneGonGluing.node K) (by simp [polygon])

@[reassoc (attr := simp)]
theorem componentι_normalizationOver (i : Fin 1) :
    PolygonPinching.componentι K 1 i ≫ normalizationOver K =
      Over.homMk (normalization K) (normalization_toBase K) := by
  simp [PolygonPinching.componentι, normalizationOver]

@[reassoc]
theorem nodeι_nodes (i : Fin 1) :
    (PolygonPinching.nodeι K 1 i ≫ nodes K).left = bOrigin K ≫ OneGonGluing.node K := by
  simp only [PolygonPinching.nodeι, nodes, Sigma.ι_comp_desc]
  rfl

/-- The actual one-gon cocone commutes on both specified endpoints. -/
theorem cocone (hn : 0 < 1) :
    PolygonPinching.toComponents K 1 hn ≫ normalizationOver K =
      PolygonPinching.toNodes K 1 ≫ nodes K := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  simp only [PolygonPinching.toComponents, PolygonPinching.toNodes, Sigma.ι_comp_desc_assoc]
  cases b
  · change ProjectiveLine.zeroSection K ≫ PolygonPinching.componentι K 1 i ≫
      normalizationOver K = _
    rw [componentι_normalizationOver]
    apply Over.OverMorphism.ext
    exact (zero_normalization K).trans (nodeι_nodes K i).symm
  · change ProjectiveLine.infinitySection K ≫
      PolygonPinching.componentι K 1 (PolygonPinching.next hn i) ≫ normalizationOver K = _
    rw [componentι_normalizationOver]
    apply Over.OverMorphism.ext
    exact (infinity_normalization K).trans (nodeι_nodes K i).symm

end FLT.Mazur.OneGonNormalization
