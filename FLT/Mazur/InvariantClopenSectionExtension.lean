/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeClopenExtensionPullback
public import FLT.Mazur.InvariantOpenGlobalRestriction

/-!
# Full invariant extension by zero on clopen cores

The complementary open is invariant whenever the original clopen is.
Gluing its invariant section with zero retains the full two-endpoint equation.
The resulting extension preserves the entire original boundary kernel.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantClopenSectionExtension
open SchemeClopenSectionExtension SchemeEffectiveEpiSections
open InvariantOpenCoefficientRestriction InvariantOpenCoefficientGluing
variable {D X : Scheme.{0}} (p q : D ⟶ X) (U : X.Opens)
  (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hclosed : IsClosed (U : Set X))
local notation "V" => complement U hclosed

include hU in
/-- The actual open complement retains every original relation arrow. -/
theorem complement_invariant : p ⁻¹ᵁ V = q ⁻¹ᵁ V := by
  ext z
  change (p z ∉ U) ↔ (q z ∉ U)
  exact not_congr (show p z ∈ U ↔ q z ∈ U from
    Iff.of_eq (congrArg (fun W : D.Opens ↦ z ∈ W) hU))

/-- Extension by zero is invariant for the full relation, not only at geometric points. -/
theorem extend_mem (s : coefficients p q U hU) :
    extend U V (inf_complement U hclosed) (sup_complement U hclosed) s.val ∈
      compatibleFunctions p q := by
  let W : Bool → X.Opens := fun b ↦ if b then U else V
  have hi : ∀ b, p ⁻¹ᵁ W b = q ⁻¹ᵁ W b := by
    intro b
    cases b
    · exact complement_invariant p q U hU hclosed
    · exact hU
  apply invariant_of_local p q W hi (by
    simp only [W, iSup_bool_eq, Bool.false_eq_true, ite_false, ite_true]
    exact sup_complement U hclosed)
  intro b
  cases b
  · change (V).ι.appTop _ ∈ coefficients p q V _
    rw [extend_right]
    exact (coefficients p q V _).zero_mem
  · change U.ι.appTop _ ∈ coefficients p q U _
    rw [extend_left]
    exact s.property

/-- The full invariant extension uses the literal extension of the underlying section. -/
def extension (s : coefficients p q U hU) : compatibleFunctions p q :=
  ⟨extend U V (inf_complement U hclosed) (sup_complement U hclosed) s.val,
    extend_mem p q U hU hclosed s⟩

/-- Restriction recovers the entire given invariant coefficient. -/
theorem restriction_extension (s : coefficients p q U hU) :
    globalRestriction p q U hU (extension p q U hU hclosed s) = s := by
  apply Subtype.ext
  exact extend_left U V (inf_complement U hclosed) (sup_complement U hclosed) s.val

/-- Every full homogeneous boundary error extends with no scalar multiplier. -/
theorem extension_boundary_zero (I : X.IdealSheafData) (s : coefficients p q U hU)
    (hs : (I.comap U.ι).subschemeι.appTop s.val = 0) :
    I.subschemeι.appTop (extension p q U hU hclosed s).val = 0 :=
  extend_boundary_zero U V (inf_complement U hclosed) (sup_complement U hclosed) I s.val hs

end FLT.Mazur.InvariantClopenSectionExtension
