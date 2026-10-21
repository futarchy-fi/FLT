/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCoefficientEmbeddingRefinement

/-!
# A common finite model for independently chosen embedding supports

The union of two finite supports gives one actual finite coefficient subring
and one whole-cubic embedding. Both independent models recover to it by the
proved Cartesian squares, and their entire pulled-back ideals agree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates
open WeierstrassIntegralChart OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R G : Type} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)

/-- Enlarging the requested support enlarges the actual coefficient subring. -/
theorem modelRing_monotone {s u : Set R} (h : s ⊆ u) :
    modelRing t j φ s ≤ modelRing t j φ u := by
  apply Algebra.adjoin_mono
  exact Set.union_subset_union (Set.union_subset_union h (Set.Subset.refl _))
    (Set.Subset.refl _)

/-- Both independent supports occur in the same explicitly constructed model ring. -/
theorem commonModelRing_inclusions (s u : Set R) :
    modelRing t j φ s ≤ modelRing t j φ (s ∪ u) ∧
      modelRing t j φ u ≤ modelRing t j φ (s ∪ u) :=
  ⟨modelRing_monotone t j φ Set.subset_union_left,
    modelRing_monotone t j φ Set.subset_union_right⟩

/-- The explicit common model still uses finitely many integer coefficients. -/
theorem commonModelRing_finiteType [Finite G] (s u : Set R)
    (hs : s.Finite) (hu : u.Finite) : Algebra.FiniteType ℤ (modelRing t j φ (s ∪ u)) :=
  modelRing_finiteType t j φ (s ∪ u) (hs.union hu)

/-- Independent finite supports have a common finite whole-embedding comparison. -/
theorem exists_common_finite_embedding_model [Finite G] (s u : Set R)
    (hs : s.Finite) (hu : u.Finite) :
    ∃ (v : Set R) (_ : v.Finite) (_ : Algebra.FiniteType ℤ (modelRing t j φ v))
      (hS : modelRing t j φ s ≤ modelRing t j φ v)
      (hU : modelRing t j φ u ≤ modelRing t j φ v),
      IsPullback
        (Spec.map (CommRingCat.ofHom (CharacterCoefficientCommonRefinement.inclusion hS)))
        (modelCurveMap t j φ v) (modelCurveMap t j φ s)
        (refinementCurveProjection t j φ s v hS) ∧
      IsPullback
        (Spec.map (CommRingCat.ofHom (CharacterCoefficientCommonRefinement.inclusion hU)))
        (modelCurveMap t j φ v) (modelCurveMap t j φ u)
        (refinementCurveProjection t j φ u v hU) := by
  obtain ⟨hS, hU⟩ := commonModelRing_inclusions t j φ s u
  exact ⟨s ∪ u, hs.union hu, commonModelRing_finiteType t j φ s u hs hu, hS, hU,
    refinementCurveMap_isPullback t j φ s (s ∪ u) hS,
    refinementCurveMap_isPullback t j φ u (s ∪ u) hU⟩

/-- The common whole curve identifies the full ideals of two independent closed models. -/
theorem commonModel_ideals_eq [Finite G] (s u : Set R)
    (hs : Function.Surjective (modelCoordinates t j φ s))
    (hu : Function.Surjective (modelCoordinates t j φ u)) :
    (modelCurveMap t j φ s).ker.comap
      (refinementCurveProjection t j φ s (s ∪ u)
        (commonModelRing_inclusions t j φ s u).1) =
      (modelCurveMap t j φ u).ker.comap
        (refinementCurveProjection t j φ u (s ∪ u)
          (commonModelRing_inclusions t j φ s u).2) := by
  rw [← refinementCurveMap_ideal t j φ s (s ∪ u) _ hs,
    ← refinementCurveMap_ideal t j φ u (s ∪ u) _ hu]

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
