/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyRing
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Field coordinates on spectrum cohomology

The spectrum global-section ring is a field with its existing ring operations.
Changing its coordinates to the original field preserves the dimension of the
actual sheaf cohomology, with the original structural scalar action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SpectrumFieldCohomologyCoordinates
open FCurve
universe u
variable (k : Type u) [Field k]

/-- The existing ring of global functions on a field spectrum carries a field structure. -/
@[instance_reducible]
def globalSectionsField : Field Γ(Spec (CommRingCat.of k), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField

variable {k} {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules)

/-- The actual cohomology has the same dimension in spectrum-ring and field coordinates. -/
theorem cohomology_finrank (n : ℕ) :
    Module.finrank Γ(Spec (CommRingCat.of k), ⊤) (ModuleRingH f.appTop.hom M n) =
      Module.finrank k (ModuleScalarH f M n) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hr := rank_eq_of_equiv_equiv e.symm
    (show ModuleScalarH f M n ≃+ ModuleRingH f.appTop.hom M n from AddEquiv.refl _)
    e.symm.bijective (fun _ _ ↦ rfl)
  exact (congrArg Cardinal.toNat hr).symm

end FLT.Mazur.SpectrumFieldCohomologyCoordinates
