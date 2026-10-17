/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteFiberInterior

/-!
# Finite target neighborhoods survive arbitrary base change

The whole restricted map remains finite after a cartesian change of base.
This transports actual finite neighborhoods, rather than merely finite fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P Y Z X : Scheme} {a : P ⟶ Y} {b : P ⟶ Z} {f : Y ⟶ X} {g : Z ⟶ X}
  (H : IsPullback a b f g)

include H in
/-- Restricting a cartesian map over a finite neighborhood keeps the full map finite. -/
theorem finite_restrict_of_isPullback (B : X.Opens) [IsFinite (f ∣_ B)] :
    IsFinite (b ∣_ (g ⁻¹ᵁ B)) := by
  have hle : b ⁻¹ᵁ (g ⁻¹ᵁ B) ≤ a ⁻¹ᵁ (f ⁻¹ᵁ B) := by
    rw [← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]
  have HB : IsPullback
      (a.resLE (f ⁻¹ᵁ B) (b ⁻¹ᵁ (g ⁻¹ᵁ B)) hle)
      (b ∣_ (g ⁻¹ᵁ B)) (f ∣_ B) (g ∣_ B) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE H (le_rfl : g ⁻¹ᵁ B ≤ g ⁻¹ᵁ B)
        (le_rfl : f ⁻¹ᵁ B ≤ f ⁻¹ᵁ B) (inf_eq_right.mpr hle).symm
  exact MorphismProperty.of_isPullback HB inferInstance

include H in
/-- Every old finite target neighborhood supplies a new one after base change. -/
theorem preimage_finiteTargetOpen_le :
    g ⁻¹ᵁ finiteTargetOpen f ≤ finiteTargetOpen b := by
  intro z hz
  obtain ⟨B, hB, hzB⟩ := (mem_finiteTargetOpen f (g z)).mp hz
  let _ := hB
  exact (mem_finiteTargetOpen b z).mpr
    ⟨g ⁻¹ᵁ B, finite_restrict_of_isPullback H B, hzB⟩

end FLT.Mazur.SchemeOpenEnvelope
