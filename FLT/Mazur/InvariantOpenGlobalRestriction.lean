/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenCoefficientRestriction

/-!
# Global invariant coefficients on every invariant open

The full relation restricts a global coefficient to any invariant source
open. Refinement retains the literal original section restriction. These
maps supply the common reference for homogeneous overlap corrections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenCoefficientRestriction
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D X : Scheme.{0}} (p q : D ⟶ X)
  (U : X.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)

/-- Restrict an original full invariant to an actual invariant open. -/
def globalRestriction : compatibleFunctions p q →+* coefficients p q U hU :=
  relationPullback p q _ _ U.ι (p ⁻¹ᵁ U).ι
    (Scheme.Hom.resLE_comp_ι p le_rfl).symm (Scheme.Hom.resLE_comp_ι q hU.le).symm

/-- Global invariant restriction retains the original structure-sheaf map. -/
theorem globalRestriction_val (w : compatibleFunctions p q) :
    (globalRestriction p q U hU w).val = U.ι.appTop w.val := rfl

/-- Restricting a global invariant through an intermediate open agrees with direct restriction. -/
theorem restriction_globalRestriction (V : X.Opens) (hV : p ⁻¹ᵁ V = q ⁻¹ᵁ V)
    (h : V ≤ U) (w : compatibleFunctions p q) :
    restriction p q U V hU hV h (globalRestriction p q U hU w) =
      globalRestriction p q V hV w := by
  apply Subtype.ext
  change (X.homOfLE h ≫ U.ι).appTop w.val = V.ι.appTop w.val
  rw [Scheme.homOfLE_ι]

end FLT.Mazur.InvariantOpenCoefficientRestriction
