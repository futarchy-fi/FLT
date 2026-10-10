/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardQuotient

/-!
# Actual sheaf twists witnessing relative Picard equality

Equality modulo base pullback is equivalent to an isomorphism with the tensor
product by an actual line bundle from the base. The base line is retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemePicard
open FCurve
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Relative equality can be witnessed by a base twist without taking a difference. -/
theorem relativeClass_eq_iff_base_twist (a b : Pic X) :
    relativeClass f a = relativeClass f b ↔ ∃ c : Pic S, b = a * pullback f c := by
  rw [relativeClass_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, mul_inv_cancel_left]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [inv_mul_cancel_left]⟩

/-- Equality of relative line classes supplies the actual twisting line and sheaf isomorphism. -/
theorem relativeClass_mk_eq_iff_twist_iso {L N : X.Modules}
    (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N) :
    relativeClass f (mk L hL) = relativeClass f (mk N hN) ↔
      ∃ B : LineBundle S, Nonempty
        (N ≅ ModuleSheafTensor.tensor L ((Scheme.Modules.pullback f).obj B.val)) := by
  rw [relativeClass_eq_iff_base_twist]
  constructor
  · rintro ⟨c, hc⟩
    induction c using inductionOn with | h B hB =>
      refine ⟨⟨B, hB⟩, (mk_eq_mk_iff hN (hL.tensor (hB.pullback f))).mp ?_⟩
      exact hc
  · rintro ⟨⟨B, hB⟩, ⟨e⟩⟩
    exact ⟨mk B hB, mk_eq_of_iso hN (hL.tensor (hB.pullback f)) e⟩

end FLT.Mazur.SchemePicard
