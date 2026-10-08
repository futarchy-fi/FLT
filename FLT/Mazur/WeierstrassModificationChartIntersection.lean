/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationGluing

/-!
# The two modification charts intersect only along the prescribed overlap

The locally directed gluing construction identifies points precisely when
they come from the common incidence principal open. This supplies the
separation statement needed to prove that the descended y-chart is open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Equal points in the two glued charts come from their actual common open. -/
theorem xChart_eq_dividedChart_iff
    (x : Spec (.of (Coordinate W s b3 b4 b6)))
    (d : Spec (.of (WeierstrassDilatation.Coordinate W s b3 b4 b6))) :
    xChart W s b3 b4 b6 x = dividedChart W s b3 b4 b6 d ↔
      ∃ z, xOpenInclusion W s b3 b4 b6 z = x ∧ overlapToDivided W s b3 b4 b6 z = d := by
  constructor
  · intro h
    obtain ⟨k, ki, kj, z, hx, hd⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (span (xOpenInclusion W s b3 b4 b6) (overlapToDivided W s b3 b4 b6))).mp h
    cases k with
    | none =>
      have hi : ki = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      have hj : kj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      subst ki
      subst kj
      exact ⟨z, hx, hd⟩
    | some k =>
      cases k with
      | left => cases kj
      | right => cases ki
  · rintro ⟨z, rfl, rfl⟩
    exact congrArg (fun f => f z) (chart_overlap W s b3 b4 b6)

/-- A point of the x chart also in the divided chart has invertible incidence coordinate. -/
theorem xChart_mem_dividedChart (x : Spec (.of (Coordinate W s b3 b4 b6)))
    (h : xChart W s b3 b4 b6 x ∈ Set.range (dividedChart W s b3 b4 b6)) :
    t W s b3 b4 b6 ∉ x.asIdeal := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨z, hz, _⟩ := (xChart_eq_dividedChart_iff W s b3 b4 b6 x d).mp hd.symm
  have hr : x ∈ Set.range (xOpenInclusion W s b3 b4 b6) := ⟨z, hz⟩
  change x ∈ Set.range (PrincipalAffineRefinement.inclusion (t W s b3 b4 b6)) at hr
  rwa [PrincipalAffineRefinement.range_inclusion] at hr

end FLT.Mazur.WeierstrassModificationX
