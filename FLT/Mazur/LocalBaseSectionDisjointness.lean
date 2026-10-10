/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Disjoint sections over a local base

For a separated family, sections with different closed specializations have
disjoint images. Any intersection specializes into the closed image of a section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FLT.Mazur.LocalBaseSectionDisjointness

universe u

variable {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
  (p : X ⟶ Spec R) [IsSeparated p]
  (s t : Spec R ⟶ X) (hs : s ≫ p = 𝟙 _) (ht : t ≫ p = 𝟙 _)

omit [IsLocalRing R] in
include hs in
/-- A section of the separated family has closed image. -/
theorem section_isClosedImmersion : IsClosedImmersion s := by
  let _ : IsClosedImmersion (s ≫ p) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s p

include hs ht in
/-- Distinct closed specializations force disjoint images over the entire local spectrum. -/
theorem disjoint_of_closedPoint_ne (hne : s (closedPoint R) ≠ t (closedPoint R)) :
    Disjoint (Set.range s) (Set.range t) := by
  let _ := section_isClosedImmersion p t ht
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hxt
  have hc : IsClosed (s ⁻¹' Set.range t) :=
    t.isClosedEmbedding.isClosed_range.preimage s.continuous
  obtain ⟨y, hy⟩ := (specializes_closedPoint x).mem_closed hc hxt
  have hey : y = closedPoint R := by
    have he := congrArg p hy
    change (t ≫ p) y = (s ≫ p) (closedPoint R) at he
    rw [hs, ht] at he
    exact he
  exact hne (hy.symm.trans (congrArg t hey))

end FLT.Mazur.LocalBaseSectionDisjointness
