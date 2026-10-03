/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicNodeChart
public import FLT.Mazur.OneGonNormalizationTorus
/-!
# The node map is a closed immersion

On each node chart the node map is a surjective ring quotient. Its pullback
over the one-gon torus is empty. Locality and cocone comparison give the result
for every positive-size polygon, hence its node map is finite and affine.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.PolygonNodesClosed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type u) [Field K]
instance cyclic (n : ℕ) (hn : 2 ≤ n) :
    IsClosedImmersion (PolygonCyclicAtlas.nodes K n hn).left := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (PolygonCyclicNormalizationFinite.targetCover K n hn)
  intro i
  change IsClosedImmersion (pullback.snd (PolygonCyclicAtlas.nodes K n hn).left
    (PolygonCyclicAtlas.chart K n hn i))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (CyclicNodeChart.specified_isPullback K n hn i).flip.isoPullback.hom,
    (CyclicNodeChart.specified_isPullback K n hn i).flip.isoPullback_hom_snd]
  exact IsClosedImmersion.spec_of_surjective _ fun a ↦
    ⟨algebraMap K _ a, (PolygonNodePresentation.aEval (R := K)).commutes a⟩
instance oneGon : IsClosedImmersion (OneGonNormalization.nodes K).left := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (OneGonNormalizationFinite.targetCover K)
  intro b
  cases b
  · change IsClosedImmersion (pullback.snd (OneGonNormalization.nodes K).left
      (OneGonGluing.node K))
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
      (OneGonNormalizationChart.node_isPullback K).flip.isoPullback.hom,
      (OneGonNormalizationChart.node_isPullback K).flip.isoPullback_hom_snd]
    exact IsClosedImmersion.spec_of_surjective _ fun a ↦
      ⟨algebraMap K _ a, (PolygonNodePresentation.bEval (R := K)).commutes a⟩
  · change IsClosedImmersion (pullback.snd (OneGonNormalization.nodes K).left
      (OneGonGluing.torus K))
    have : IsEmpty ↑(pullback (OneGonNormalization.nodes K).left (OneGonGluing.torus K)) := by
      apply Scheme.isEmpty_pullback
      rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ hy
      have hx : x ∈ (OneGonNormalization.nodes K).left ⁻¹ᵁ
          (OneGonGluing.torus K).opensRange := hy
      rw [OneGonNormalizationTorus.nodes_preimage_torus] at hx
      exact hx
    infer_instance
instance atlas (n : ℕ) [NeZero n] : IsClosedImmersion (PolygonAtlas.nodes K n).left := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact oneGon K
  · exact cyclic K (n + 2) (by omega)
open PolygonPinching
variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
theorem cocone : IsClosedImmersion q.left := by
  have : IsIso (polygonIso K n hn p q h).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonIso K n hn p q h).hom))
  rw [← nodes_polygonIso K n hn p q h]
  change IsClosedImmersion ((PolygonAtlas.nodes K n).left ≫ _)
  infer_instance
end FLT.Mazur.PolygonNodesClosed
