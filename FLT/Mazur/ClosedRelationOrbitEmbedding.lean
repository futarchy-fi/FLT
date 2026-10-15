/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOrbitTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed invariant restrictions of actual orbit spaces

A Cartesian restriction of an internal scheme relation to a closed invariant
source gives a closed embedding on orbit spaces. The proof uses actual points
of scheme pullbacks, and does not identify their carriers with set pullbacks.
This is a topological result; it does not assert scheme quotient effectivity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
namespace FLT.Mazur.RelativeRelationOrbit
universe u
variable {S : Scheme.{u}} {A U C B : Over S} {p q : A ⟶ U} {r s : C ⟶ B}
  (e : CategoryTheory.EquivalenceRelation p q)
  (ec : CategoryTheory.EquivalenceRelation r s) (i : B ⟶ U) (z : C ⟶ A)
  (hp : z ≫ p = r ≫ i) (hq : z ≫ q = s ≫ i)
include hp hq

/-- The original orbit of a closed source point is constant on the closed relation. -/
theorem closedOrbit_invariant (a : C.left) :
    projection e (i.left (r.left a)) = projection e (i.left (s.left a)) := by
  have h₁ := congrArg (fun f ↦ f.left a) hp
  have h₂ := congrArg (fun f ↦ f.left a) hq
  exact (congrArg (projection e) h₁).symm.trans
    ((projection_pair e (z.left a)).trans (congrArg (projection e) h₂))

/-- The canonical map from the full closed orbit space into the original orbit space. -/
def closedOrbitMap : Orbit ec → Orbit e :=
  descend ec (projection e ∘ i.left) (closedOrbit_invariant e i z hp hq)

/-- The quotient comparison keeps the original source point. -/
theorem closedOrbitMap_projection (x : B.left) :
    closedOrbitMap e ec i z hp hq (projection ec x) = projection e (i.left x) := rfl

/-- The quotient comparison is continuous for the actual quotient topologies. -/
theorem closedOrbitMap_continuous : Continuous (closedOrbitMap e ec i z hp hq) :=
  descend_continuous ec _ _ ((projection_continuous e).comp i.left.continuous)

variable [IsClosedImmersion i.left]
  (H : IsPullback z.left r.left p.left i.left)
include H

/-- Every original relation arrow between closed points lifts to the closed relation. -/
theorem closed_related_iff (x y : B.left) :
    Related r s x y ↔ Related p q (i.left x) (i.left y) := by
  constructor
  · rintro ⟨a, ha, hb⟩
    refine ⟨z.left a, ?_, ?_⟩
    · exact (congrArg (fun f ↦ f.left a) hp).trans (congrArg i.left ha)
    · exact (congrArg (fun f ↦ f.left a) hq).trans (congrArg i.left hb)
  · rintro ⟨a, ha, hb⟩
    obtain ⟨w, hw, hx⟩ := Scheme.exists_preimage_of_isPullback H a x ha
    refine ⟨w, hx, i.left.isClosedEmbedding.injective ?_⟩
    exact (congrArg (fun f ↦ f.left w) hq).symm.trans ((congrArg q.left hw).trans hb)

/-- The closed quotient retains exactly the original orbits, with no extra identifications. -/
theorem closedOrbitMap_injective : Function.Injective (closedOrbitMap e ec i z hp hq) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := projection_surjective ec a
  obtain ⟨y, rfl⟩ := projection_surjective ec b
  apply (projection_eq_iff ec x y).mpr
  exact (closed_related_iff i z hp hq H x y).mpr ((projection_eq_iff e _ _).mp hab)

omit [IsClosedImmersion i.left] in
/-- Saturation of a subset of the closed quotient is already its image in the source. -/
theorem closedOrbitMap_preimage_image (W : Set (Orbit ec)) :
    projection e ⁻¹' (closedOrbitMap e ec i z hp hq '' W) =
      i.left '' (projection ec ⁻¹' W) := by
  ext t
  constructor
  · rintro ⟨v, hv, he⟩
    obtain ⟨x, rfl⟩ := projection_surjective ec v
    obtain ⟨a, ha, ht⟩ := (projection_eq_iff e (i.left x) t).mp he
    obtain ⟨w, hw, hx⟩ := Scheme.exists_preimage_of_isPullback H a x ha
    refine ⟨s.left w, ?_, ?_⟩
    · change projection ec (s.left w) ∈ W
      rw [← projection_pair ec w, hx]
      exact hv
    · exact (congrArg (fun f ↦ f.left w) hq).symm.trans ((congrArg q.left hw).trans ht)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨projection ec x, hx, rfl⟩

/-- The closed quotient comparison sends every closed set to a closed set. -/
theorem closedOrbitMap_isClosedMap : IsClosedMap (closedOrbitMap e ec i z hp hq) := by
  intro W hW
  apply (projection_isQuotientMap e).isClosed_preimage.mp
  rw [closedOrbitMap_preimage_image e ec i z hp hq H]
  exact i.left.isClosedEmbedding.isClosedMap _ (hW.preimage (projection_continuous ec))

/-- The full invariant closed quotient is a closed topological subspace of the original quotient. -/
theorem closedOrbitMap_isClosedEmbedding :
    IsClosedEmbedding (closedOrbitMap e ec i z hp hq) :=
  .of_continuous_injective_isClosedMap (closedOrbitMap_continuous e ec i z hp hq)
    (closedOrbitMap_injective e ec i z hp hq H) (closedOrbitMap_isClosedMap e ec i z hp hq H)

end FLT.Mazur.RelativeRelationOrbit
