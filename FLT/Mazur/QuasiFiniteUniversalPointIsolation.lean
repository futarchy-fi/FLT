/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiFiniteGeometricPointIsolation

/-!
# Point isolation independent of the lifting field

A chosen field-valued point factors through one affine original open whose
fiber support is a singleton. The support statement applies to every point
of the open, so independent lifts over different fields remain covered.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.QuasiFiniteUniversalPointIsolation
set_option backward.isDefEq.respectTransparency false
variable {E S : Scheme} (e : E ⟶ S) [LocallyQuasiFinite e] [LocallyOfFiniteType e]

/-- One affine original neighborhood isolates the support for lifts over every field. -/
theorem exists_factor {L : Type} [Field L] (z : Spec (.of L) ⟶ E) :
    ∃ (A : Scheme) (q : A ⟶ E) (w : Spec (.of L) ⟶ A),
      IsAffine A ∧ IsOpenImmersion q ∧ w ≫ q = z ∧
      ∀ y : A, e (q y) = e (z default) → q y = z default := by
  obtain ⟨U, hU, hz, hsingle⟩ :=
    QuasiFiniteGeometricPointIsolation.exists_affine_open e (z default)
  have hr : Set.range z ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim x default]
    exact hz
  let w := IsOpenImmersion.lift U.ι z hr
  exact ⟨U.toScheme, U.ι, w, hU, inferInstance,
    IsOpenImmersion.lift_fac _ _ _, fun y hy ↦ hsingle _ y.property hy⟩

end FLT.Mazur.QuasiFiniteUniversalPointIsolation
