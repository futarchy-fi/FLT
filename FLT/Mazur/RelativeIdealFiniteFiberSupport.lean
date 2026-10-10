/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealFamilies
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite ambient supports of full relative ideal fibers

The support uses every point of the actual closed subscheme fiber, including
points with nontrivial residue extensions. Finiteness follows from the finite
projection, rather than from a choice of rational points or sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A S X : Scheme.{u}} (a : A ⟶ S) (d : ℕ) (s : X ⟶ S)
variable (J : RelativeIdealFamilies a d s) (x : X)

/-- The ambient image of the entire actual subscheme fiber. -/
def relativeIdealFiberSupport : Set A :=
  (J.val.subschemeι ≫ pullback.snd s a) ''
    ((J.val.subschemeι ≫ pullback.fst s a) ⁻¹' {x})

/-- Every full finite locally free ideal family has finite ambient fiber support. -/
theorem relativeIdealFiberSupport_finite : (relativeIdealFiberSupport a d s J x).Finite := by
  let _ : IsFinite (J.val.subschemeι ≫ pullback.fst s a) := J.property.1
  exact ((J.val.subschemeι ≫ pullback.fst s a).finite_preimage_singleton x).image _

/-- Containment of this finite support is exactly containment of all actual fiber points. -/
theorem relativeIdealFiberSupport_subset_iff (T : Set A) :
    relativeIdealFiberSupport a d s J x ⊆ T ↔
      ∀ y : J.val.subscheme, (J.val.subschemeι ≫ pullback.fst s a) y = x →
        (J.val.subschemeι ≫ pullback.snd s a) y ∈ T := by
  constructor
  · intro h y hy
    exact h ⟨y, hy, rfl⟩
  · rintro h _ ⟨y, hy, rfl⟩
    exact h y hy

end FLT.Mazur.ClosedIdealCover
