/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRing

/-!
# The two generators of any arithmetic node image

An algebra containing the two coordinate images contains the image of every
function on the full smoothing chart. This works for arbitrary target
subalgebras, including finite extensions of the original node algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (t : R) (f : ChartRing t →ₐ[R] A) (C : Subalgebra R A)

/-- Two coordinate membership proofs construct a factorization of the entire node map. -/
def rangeFactor (hx : f (leftCoordinate t) ∈ C) (hy : f (rightCoordinate t) ∈ C) :
    ChartRing t →ₐ[R] C :=
  evaluate t ⟨f (leftCoordinate t), hx⟩ ⟨f (rightCoordinate t), hy⟩ (by
    apply Subtype.ext
    change f (leftCoordinate t) * f (rightCoordinate t) = algebraMap R A t
    rw [← map_mul, coordinate_relation, AlgHom.commutes])

/-- The factorization retains the full original map, not only its coordinate values. -/
theorem rangeFactor_comp (hx : f (leftCoordinate t) ∈ C)
    (hy : f (rightCoordinate t) ∈ C) :
    C.val.comp (rangeFactor t f C hx hy) = f := by
  apply chartRing_hom_ext t
  · change ((rangeFactor t f C hx hy) (leftCoordinate t)).val = _
    rw [rangeFactor, evaluate_left]
  · change ((rangeFactor t f C hx hy) (rightCoordinate t)).val = _
    rw [rangeFactor, evaluate_right]

/-- Membership of the two generators detects containment of the whole function image. -/
theorem range_le_iff_coordinates :
    f.range ≤ C ↔ f (leftCoordinate t) ∈ C ∧ f (rightCoordinate t) ∈ C := by
  constructor
  · intro hf
    exact ⟨hf (f.mem_range_self _), hf (f.mem_range_self _)⟩
  · rintro ⟨hx, hy⟩ z ⟨w, rfl⟩
    have he := AlgHom.congr_fun (rangeFactor_comp t f C hx hy) w
    exact he ▸ ((rangeFactor t f C hx hy) w).property

end FLT.Mazur.PolygonSmoothing
