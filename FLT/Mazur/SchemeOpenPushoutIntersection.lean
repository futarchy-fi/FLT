/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeOpenPushoutCharts

/-!
# The full intersection in an open scheme pushout

The two charts intersect exactly along the original common open subscheme.
This identifies the gluing square as a pullback, including all its points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeOpenPushout
universe u
variable {O E X : Scheme.{u}} (e : O ⟶ E) (x : O ⟶ X)
  [IsOpenImmersion e] [IsOpenImmersion x]

/-- Equal images of opposite charts come from the prescribed overlap. -/
theorem inl_eq_inr_iff (a : E) (b : X) :
    pushout.inl e x a = pushout.inr e x b ↔ ∃ o, e o = a ∧ x o = b := by
  change colimit.ι (span e x) WalkingSpan.left a =
    colimit.ι (span e x) WalkingSpan.right b ↔ _
  rw [Scheme.IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨i, fi, fj, o, hi, hj⟩
    cases i with
    | none =>
      cases fi
      cases fj
      exact ⟨o, hi, hj⟩
    | some i =>
      cases i with
      | left => cases fj
      | right => cases fi
  · rintro ⟨o, ho, hx⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, o, ho, hx⟩

/-- The inverse image of the exterior chart is precisely the common open. -/
theorem inr_preimage_inl :
    (pushout.inr e x) ⁻¹' Set.range (pushout.inl e x) = Set.range x := by
  ext b
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨o, _, ho⟩ := (inl_eq_inr_iff e x a b).mp ha
    exact ⟨o, ho⟩
  · rintro ⟨o, rfl⟩
    exact ⟨e o, congrArg (fun f => f o) (pushout.condition (f := e) (g := x))⟩

/-- Open gluing identifies the entire fiber product of its two charts. -/
theorem isPullback : IsPullback e x (pushout.inl e x) (pushout.inr e x) := by
  apply IsOpenImmersion.isPullback e x (pushout.inl e x) (pushout.inr e x)
    pushout.condition.symm
  exact TopologicalSpace.Opens.ext (inr_preimage_inl e x)

end FLT.Mazur.SchemeOpenPushout
