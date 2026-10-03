/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveNodeOpenImmersion

/-!
# Descent of the node condition through open charts

Closed points lift to closed points in an open chart. Smoothness and the
completed-stalk node model then descend from a covering family.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.CurveNodeOpenCover
open FCurve.CurveNode
variable {K : Type u} [Field K] {X U : Scheme.{u}}
variable (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]

theorem at_image (j : U ⟶ X) [IsOpenImmersion j]
    (h : AtWorstNodes (j ≫ f)) (x : U) (hx : IsClosed ({j x} : Set X)) :
    j x ∈ f.smoothLocus ∨ IsNode f (j x) := by
  have he : j ⁻¹' ({j x} : Set X) = {x} := by
    ext y
    exact j.isOpenEmbedding.injective.eq_iff
  have hc : IsClosed ({x} : Set U) := by
    rw [← he]
    exact hx.preimage j.continuous
  rcases h x hc with hs | hn
  · left
    change x ∈ j ⁻¹ᵁ f.smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact hs
  · exact Or.inr ((CurveNodeOpenImmersion.isNode_iff j f x).mpr hn)

/-- The closed-point node condition descends from an open cover. -/
theorem of_openCover (U : X.OpenCover) (h : ∀ i, AtWorstNodes (U.f i ≫ f)) :
    AtWorstNodes f := by
  intro x hx
  obtain ⟨y, hy⟩ := U.covers x
  have hi := at_image f (U.f _) (h _) y (by rwa [hy])
  simpa only [hy] using hi

/-- Transport the node condition along a surjective open immersion. -/
theorem of_surjective (j : U ⟶ X) [IsOpenImmersion j]
    (hj : Function.Surjective j) (h : AtWorstNodes (j ≫ f)) : AtWorstNodes f := by
  intro x hx
  obtain ⟨y, rfl⟩ := hj x
  exact at_image f j h y hx
end FLT.Mazur.CurveNodeOpenCover
