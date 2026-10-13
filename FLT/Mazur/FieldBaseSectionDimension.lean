/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechZeroSections
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimensions of sections with the actual spectral base action

The global sections of Spec K are canonically K. This comparison identifies
the rank of actual sections over those global functions with scalar H0.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

open Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] {X : Scheme} (f : X ⟶ Spec (.of K)) (M : X.Modules)

/-- The actual spectral-base section rank agrees with field-valued degree-zero cohomology. -/
theorem baseSections_finrank_eq_scalarH0 :
    Module.finrank Γ(Spec (.of K), ⊤) (baseSections M f.appTop.hom ⊤) =
      Module.finrank K (ModuleScalarH f M 0) := by
  let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  let j : ModuleScalarH f M 0 ≃+ baseSections M f.appTop.hom ⊤ :=
    (moduleH0Equiv M).toAddEquiv
  have hr :=
    lift_rank_eq_of_equiv_equiv e j e.bijective (by
      intro a x
      change (moduleH0Equiv M) ((structureScalarMap f a) • (show ModuleH M 0 from x)) =
        ((X.presheaf.map (homOfLE (show ⊤ ≤ ⊤ from le_rfl)).op).hom
          (f.appTop.hom (e a))) • (moduleH0Equiv M) x
      rw [show homOfLE (show ⊤ ≤ ⊤ from le_rfl) = 𝟙 (⊤ : X.Opens) from rfl,
        op_id, CategoryTheory.Functor.map_id]
      exact (moduleH0Equiv M).map_smul (structureScalarMap f a) x)
  simpa only [Module.finrank, Cardinal.toNat_lift] using congrArg Cardinal.toNat hr.symm

end FLT.Mazur.FCurve
