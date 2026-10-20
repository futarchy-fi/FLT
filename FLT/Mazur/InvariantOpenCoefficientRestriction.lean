/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantFunctorial

/-!
# Full invariant coefficients restrict to smaller invariant opens

The source restriction and both full relation endpoints give a ring map.
Compositions are literal restriction, so overlaps can be compared without
choosing a new presentation of their invariant rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantOpenCoefficientRestriction
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{0}} (p q : D ⟶ A)

/-- Full invariant sections on a prescribed invariant source open. -/
abbrev coefficients (U : A.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) :=
  compatibleFunctions (p.resLE U _ le_rfl) (q.resLE U _ hU.le)

variable (U V : A.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
  (hV : p ⁻¹ᵁ V = q ⁻¹ᵁ V) (h : V ≤ U)

/-- A smaller invariant open retains the full relation over each of its points. -/
def restriction : coefficients p q U hU →+* coefficients p q V hV := by
  let v := D.homOfLE (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ hx ↦ h hx)
  refine relationPullback _ _ _ _ (A.homOfLE h) v ?_ ?_
  · apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc, v]
  · apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc, v]

/-- Invariant restriction is the underlying original section restriction. -/
theorem restriction_val (s : coefficients p q U hU) :
    (restriction p q U V hU hV h s).val = (A.homOfLE h).appTop s.val := rfl

/-- Every path through nested invariant domains induces the same coefficient. -/
theorem restriction_comp (W : A.Opens) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W) (h' : W ≤ V)
    (s : coefficients p q U hU) :
    restriction p q V W hV hW h' (restriction p q U V hU hV h s) =
      restriction p q U W hU hW (h'.trans h) s := by
  apply Subtype.ext
  simp only [restriction_val]
  change (A.homOfLE h' ≫ A.homOfLE h).appTop s.val = _
  have he : A.homOfLE h' ≫ A.homOfLE h = A.homOfLE (h'.trans h) := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.homOfLE_ι]
  rw [he]

include hU hV in
/-- Intersections are invariant under every arrow of the full relation. -/
theorem inf_invariant : p ⁻¹ᵁ (U ⊓ V) = q ⁻¹ᵁ (U ⊓ V) := by
  change (p ⁻¹ᵁ U) ⊓ (p ⁻¹ᵁ V) = (q ⁻¹ᵁ U) ⊓ (q ⁻¹ᵁ V)
  rw [hU, hV]

end FLT.Mazur.InvariantOpenCoefficientRestriction
