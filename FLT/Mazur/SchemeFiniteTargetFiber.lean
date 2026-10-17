/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteTargetRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite point fibers on the exact finite target locus

An actual finite target neighborhood identifies its whole fiber with the
original fiber. No quasi-compactness assumption on the ambient map is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme} (p : D ⟶ A)

/-- A point in the finite target locus has a finite entire original fiber. -/
theorem finite_fiber_of_mem_finiteTarget (x : A) (hx : x ∈ finiteTargetOpen p) :
    (p ⁻¹' {x}).Finite := by
  let U := finiteTargetOpen p
  let _ := finite_restrict_finiteTarget p
  let y : U.toScheme := ⟨x, hx⟩
  have hres (z : (p ⁻¹ᵁ U).toScheme) : U.ι ((p ∣_ U) z) = p ((p ⁻¹ᵁ U).ι z) :=
    congrArg (fun f : (p ⁻¹ᵁ U).toScheme ⟶ A ↦ f z) (morphismRestrict_ι p U)
  apply (((p ∣_ U).finite_preimage_singleton y).image (p ⁻¹ᵁ U).ι).subset
  intro z hz
  let z' : (p ⁻¹ᵁ U).toScheme := ⟨z, by change p z ∈ U; rw [hz]; exact hx⟩
  exact ⟨z', Subtype.ext ((hres z').trans hz), rfl⟩

end FLT.Mazur.SchemeOpenEnvelope
