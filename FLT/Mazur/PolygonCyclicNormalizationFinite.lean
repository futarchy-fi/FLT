/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicNormalizationPullback
public import FLT.Mazur.PolygonNormalizationAlgebra
/-!
# Finite surjective normalization of the cyclic polygon

The cartesian node charts reduce finiteness to the two affine branches.
The coproduct comparison identifies this map with the specified normalization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
universe u
namespace FLT.Mazur.PolygonCyclicNormalizationFinite
open PolygonCyclicNormalizationPullback PolygonCyclicNormalizationRanges
variable (K : Type u) [Field K] (n : ℕ) (hn : 2 ≤ n)

/-- The two affine branches give a finite morphism to the node. -/
instance affine_finite : IsFinite (affineNormalization K) := by
  unfold affineNormalization
  infer_instance

/-- Every prime of the node lifts to one of its affine branches. -/
theorem affine_surjective : Function.Surjective (affineNormalization K) := by
  intro y
  obtain ⟨p, hp⟩ := PolygonNormalizationAlgebra.node_comap_surjective y
  obtain ⟨p | p, rfl⟩ := (PrimeSpectrum.primeSpectrumProd K[X] K[X]).symm.surjective p
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inl] at hp
    rw [← PrimeSpectrum.comap_comp_apply] at hp
    refine ⟨(coprod.inl : ProjectiveLine.chart K ⟶
      ProjectiveLine.chart K ⨿ ProjectiveLine.chart K) p, ?_⟩
    change (coprod.inl ≫ affineNormalization K) p = y
    simp only [affineNormalization, coprod.inl_desc]
    change PrimeSpectrum.comap (PolygonNodeEqualizer.first (R := K)).toRingHom p = y
    exact hp
  · rw [PrimeSpectrum.primeSpectrumProd_symm_inr] at hp
    rw [← PrimeSpectrum.comap_comp_apply] at hp
    refine ⟨(coprod.inr : ProjectiveLine.chart K ⟶
      ProjectiveLine.chart K ⨿ ProjectiveLine.chart K) p, ?_⟩
    change (coprod.inr ≫ affineNormalization K) p = y
    simp only [affineNormalization, coprod.inr_desc]
    change PrimeSpectrum.comap (PolygonNodeEqualizer.second (R := K)).toRingHom p = y
    exact hp

/-- The node charts cover the cyclic polygon. -/
def targetCover : (PolygonCyclicAtlas.scheme K n hn).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin n)
    (fun _ ↦ PolygonNodeBranches.node K) (PolygonCyclicAtlas.chart K n hn)
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := PolygonCyclicAtlas.charts_cover K n hn x
      exact ⟨i, y, hy⟩) (fun _ ↦ inferInstance)

/-- The normalization from the scheme coproduct is finite. -/
instance normalization_finite : IsFinite (normalization K n hn) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (targetCover K n hn)
  intro i
  change IsFinite (pullback.snd (normalization K n hn) (PolygonCyclicAtlas.chart K n hn i))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
    (isPullback K n hn i).flip.isoPullback.hom, (isPullback K n hn i).flip.isoPullback_hom_snd]
  infer_instance

/-- The normalization from the scheme coproduct is surjective. -/
theorem normalization_surjective : Function.Surjective (normalization K n hn) := by
  intro y
  obtain ⟨i, z, rfl⟩ := PolygonCyclicAtlas.charts_cover K n hn y
  obtain ⟨a, rfl⟩ := affine_surjective K z
  exact ⟨chartLift K n hn i a, congrArg (fun f ↦ f a) (chartLift_normalization K n hn i)⟩

/-- The canonical comparison between scheme and over-category coproducts. -/
abbrev comparison := sigmaComparison (Over.forget (Spec (.of K)))
  (fun _ : Fin n ↦ PolygonPinching.component K)

/-- The coproduct comparison respects the normalization maps. -/
@[reassoc] theorem comparison_normalization :
    comparison K n ≫ (PolygonCyclicAtlas.normalization K n hn).left = normalization K n hn := by
  apply Sigma.hom_ext
  intro i
  rw [ι_comp_sigmaComparison_assoc]
  change (PolygonPinching.componentι K n i ≫ PolygonCyclicAtlas.normalization K n hn).left = _
  rw [PolygonCyclicAtlas.componentι_normalization]
  simp [normalization]

/-- The specified over-category normalization is finite. -/
instance specified_finite : IsFinite (PolygonCyclicAtlas.normalization K n hn).left := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) (comparison K n),
    comparison_normalization]
  infer_instance

/-- The specified over-category normalization is surjective. -/
theorem specified_surjective :
    Function.Surjective (PolygonCyclicAtlas.normalization K n hn).left := by
  intro y
  obtain ⟨z, hz⟩ := normalization_surjective K n hn y
  exact ⟨comparison K n z, (congrArg (fun f ↦ f z) (comparison_normalization K n hn)).trans hz⟩
end FLT.Mazur.PolygonCyclicNormalizationFinite
