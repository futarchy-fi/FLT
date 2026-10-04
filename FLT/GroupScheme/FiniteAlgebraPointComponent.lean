/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteAlgebraComponents

/-! # The local factor containing a specified rational point -/

@[expose] public noncomputable section

namespace FiniteAlgebra

variable {k A : Type*} [Field k] [CommRing A] [IsArtinianRing A] [Algebra k A]

/-- A rational point selects exactly one primitive component. -/
theorem existsUnique_pointComponent (ε : A →ₐ[k] k) :
    ∃! m : ComponentIndex A, ε (componentIdempotent A m) = 1 := by
  classical
  let : Fintype (ComponentIndex A) := Fintype.ofFinite _
  have hc := (ThreeAdicPlan.componentIdempotent_complete (⊥ : Ideal A)).map ε.toRingHom
  have hex : ∃ m : ComponentIndex A, ε (componentIdempotent A m) = 1 := by
    by_contra h
    push Not at h
    have hz (m : ComponentIndex A) : ε (componentIdempotent A m) = 0 :=
      (IsIdempotentElem.iff_eq_zero_or_one.mp (hc.idem m)).resolve_right (h m)
    have hs := hc.complete
    change ∑ m, ε (componentIdempotent A m) = 1 at hs
    simp only [hz, Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, hm, fun n hn ↦ ?_⟩
  by_contra hnm
  have hh := hc.ortho hnm
  change ε (componentIdempotent A n) * ε (componentIdempotent A m) = 0 at hh
  rw [hn, hm, one_mul] at hh
  exact one_ne_zero hh

/-- The component containing the specified point. -/
def pointComponentIndex (ε : A →ₐ[k] k) : ComponentIndex A :=
  (existsUnique_pointComponent ε).choose

@[simp]
theorem point_componentIdempotent (ε : A →ₐ[k] k) :
    ε (componentIdempotent A (pointComponentIndex ε)) = 1 :=
  (existsUnique_pointComponent ε).choose_spec.1

/-- The defining ideal of the component containing the point. -/
abbrev pointComponentIdeal (ε : A →ₐ[k] k) : Ideal A :=
  Ideal.span {1 - componentIdempotent A (pointComponentIndex ε)}

/-- Its coordinate algebra as an actual quotient. -/
abbrev PointComponent (ε : A →ₐ[k] k) := A ⧸ pointComponentIdeal ε

/-- The original quotient coordinate map. -/
abbrev pointProjection (ε : A →ₐ[k] k) : A →ₐ[k] PointComponent ε :=
  Ideal.Quotient.mkₐ k _

/-- The point restricted to its component. -/
def componentPoint (ε : A →ₐ[k] k) : PointComponent ε →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ ε (by
    change Ideal.span {1 - componentIdempotent A (pointComponentIndex ε)} ≤ RingHom.ker ε
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change ε (1 - componentIdempotent A (pointComponentIndex ε)) = 0
    rw [map_sub, map_one, point_componentIdempotent, sub_self])

@[simp]
theorem componentPoint_projection (ε : A →ₐ[k] k) (x : A) :
    componentPoint ε (Ideal.Quotient.mk (pointComponentIdeal ε) x) = ε x := rfl

end FiniteAlgebra
