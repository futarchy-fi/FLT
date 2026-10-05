/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Length

/-!
# Length of a finite scheme over a field

The length is the dimension of its actual structure-sheaf global sections,
expressed using the existing scalar degree-zero cohomology. Finiteness follows
from the finite structure morphism. Positivity is equivalent to nonempty support.
This is field length, so residue-field degrees are included.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- A finite structure morphism makes the actual ring of global sections finite. -/
theorem structureScalarMap_finite [IsFinite f] : (structureScalarMap f).Finite := by
  exact f.finite_appTop.comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)

/-- Degree-zero structure cohomology of a finite scheme is finite-dimensional. -/
theorem finite_H0_of_isFinite [IsFinite f] : Module.Finite k (H0 f) := by
  let := Module.compHom Γ(X, ⊤) (structureScalarMap f)
  let : Module.Finite k Γ(X, ⊤) := structureScalarMap_finite f
  exact Module.Finite.equiv (scalarH0Equiv f).symm

/-- Global constants detect whether a scheme has a point. -/
theorem nontrivial_H0_iff : Nontrivial (H0 f) ↔ Nonempty X := by
  constructor
  · intro h
    by_contra hx
    have : IsEmpty X := not_nonempty_iff.mp hx
    have : Subsingleton (H0 f) := (scalarH0Equiv f).injective.subsingleton
    exact not_nontrivial (H0 f) h
  · intro h
    have : Nonempty X := h
    have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice h, trivial⟩⟩
    exact (scalarH0Equiv f).toEquiv.nontrivial

/-- Field length of the finite closed scheme, using its actual scalar action. -/
def finiteSchemeLength : ℕ := Module.finrank k (H0 f)

/-- Field length agrees with module length, including residue-field multiplicities. -/
theorem finiteSchemeLength_eq_module_length [IsFinite f] :
    (finiteSchemeLength f : ℕ∞) = Module.length k (H0 f) := by
  have := finite_H0_of_isFinite f
  exact (Module.length_eq_finrank k (H0 f)).symm

/-- A finite scheme over a field has positive length exactly when it has a point. -/
theorem finiteSchemeLength_pos_iff [IsFinite f] :
    0 < finiteSchemeLength f ↔ Nonempty X := by
  have := finite_H0_of_isFinite f
  exact Module.finrank_pos_iff.trans (nontrivial_H0_iff f)

/-- A finite scheme over a field has length zero exactly when it is empty. -/
theorem finiteSchemeLength_eq_zero_iff [IsFinite f] :
    finiteSchemeLength f = 0 ↔ IsEmpty X := by
  rw [← not_nonempty_iff, ← finiteSchemeLength_pos_iff f, not_lt, Nat.le_zero]

end FLT.Mazur.FCurve
