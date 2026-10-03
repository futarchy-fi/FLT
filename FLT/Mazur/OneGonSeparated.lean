/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SeparatedOpenCover
public import FLT.Mazur.OneGonOverlapGraph
public import FLT.Mazur.OneGonNormalizationFinite
/-!
# Separatedness of the one-gon

The specified gluing overlap is the actual intersection of its two affine
charts. Its closed graph and the two affine diagonals prove separatedness.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.OneGonSeparated
open OneGonGluing OneGonTransition PolygonNodePresentation
variable (K : Type u) [Field K]
/-- The prescribed puncture is the actual chart intersection. -/
theorem chart_isPullback : IsPullback (bPuncture K) (toTorus K) (node K) (torus K) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (overlap_condition K).symm
  apply TopologicalSpace.Opens.ext
  ext x
  change torus K x ∈ Set.range (node K) ↔ x ∈ Set.range (toTorus K)
  constructor
  · rintro ⟨y, hy⟩
    change colimit.ι (span (bPuncture K) (toTorus K)) WalkingSpan.left y =
      colimit.ι (span (bPuncture K) (toTorus K)) WalkingSpan.right x at hy
    obtain ⟨a, fi, fj, z, _, hz⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).mp hy
    cases fi <;> cases fj
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨bPuncture K z, congrArg (fun f ↦ f z) (overlap_condition K)⟩
/-- The product of the charts uses their specified structure maps. -/
def chartProductIso :
    pullback (node K ≫ toBase K) (torus K ≫ toBase K) ≅
      pullback (bToBase K) (torusToBase K) :=
  pullback.congrHom (node_toBase K) (torus_toBase K)
/-- The mixed chart intersection has closed graph. -/
theorem mixed_closed : IsClosedImmersion (pullback.mapDesc (node K) (torus K) (toBase K)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (chartProductIso K).hom,
    ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      (chart_isPullback K).isoPullback.hom]
  have he : (chart_isPullback K).isoPullback.hom ≫
      pullback.mapDesc (node K) (torus K) (toBase K) ≫ (chartProductIso K).hom =
      OneGonOverlapGraph.graph K := by
    apply pullback.hom_ext <;>
      simp [chartProductIso, pullback.mapDesc, OneGonOverlapGraph.graph]
  rw [he]
  infer_instance
-- The identical-chart and symmetry arguments are independent of this atlas.
/-- An identical chart pair has the separated chart diagonal. -/
theorem same_closed {U X S : Scheme.{u}} (i : U ⟶ X) [Mono i] (f : X ⟶ S)
    [IsSeparated (i ≫ f)] : IsClosedImmersion (pullback.mapDesc i i f) := by
  have he : pullback.mapDesc i i f = pullback.fst i i ≫ pullback.diagonal (i ≫ f) := by
    apply pullback.hom_ext
    · simp [pullback.mapDesc]
    · simp only [pullback.mapDesc, pullback.lift_snd, Category.comp_id,
        Category.assoc, pullback.diagonal_snd]
      exact (cancel_mono i).mp pullback.condition.symm
  rw [he]
  infer_instance
/-- Exchange the chart factors of a closed intersection graph. -/
theorem reversed_closed {U V X S : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) (f : X ⟶ S)
    [IsClosedImmersion (pullback.mapDesc i j f)] :
    IsClosedImmersion (pullback.mapDesc j i f) := by
  have he : pullback.mapDesc j i f = (pullbackSymmetry j i).hom ≫
      pullback.mapDesc i j f ≫ (pullbackSymmetry (i ≫ f) (j ≫ f)).hom := by
    apply pullback.hom_ext <;> simp [pullback.mapDesc]
  rw [he]
  infer_instance
/-- The one-gon is separated over its coefficient field. -/
theorem separated : IsSeparated (toBase K) := by
  apply SeparatedOpenCover.of_pairwise _ (OneGonNormalizationFinite.targetCover K)
  intro i j
  cases i <;> cases j
  · have : IsSeparated (node K ≫ toBase K) := by rw [node_toBase]; infer_instance
    exact same_closed (node K) (toBase K)
  · exact mixed_closed K
  · have := mixed_closed K
    exact reversed_closed (node K) (torus K) (toBase K)
  · have : IsSeparated (torus K ≫ toBase K) := by rw [torus_toBase]; infer_instance
    exact same_closed (torus K) (toBase K)
instance scheme_separated : (scheme K).IsSeparated := by
  have := separated K
  constructor
  rw [← terminal.comp_from (toBase K)]
  infer_instance
end FLT.Mazur.OneGonSeparated
