/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianClosedImageGenerizations
public import FLT.Mazur.ProperCoreResidualInterior
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite generic witnesses for the residual obstruction

The excluded residual locus is closed in the entire envelope. On a Noetherian
envelope, finitely many of its actual generic points detect all accumulation
of its image. At a full fiber the remaining interior test therefore concerns
excluded residual points over generizations, not just points over that fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.ProperCoreResidualInterior
open SchemeOpenEnvelope
universe u
variable {X Y : Scheme.{u}} (π : Y ⟶ X) (U T : Y.Opens) [NoetherianSpace Y]

omit [NoetherianSpace Y] in
/-- The excluded residual source is closed, even if its image is not closed. -/
theorem residualSource_isClosed : IsClosed {y : Y | y ∉ U ∧ y ∉ T} :=
  U.isOpen.isClosed_compl.inter T.isOpen.isClosed_compl

/-- Finitely many actual excluded residual points control the entire residual image closure. -/
theorem exists_finite_residual_generizations :
    ∃ F : Set Y, F.Finite ∧ (∀ y ∈ F, y ∉ U ∧ y ∉ T) ∧
      ∀ x : X, x ∈ closure (residualBadImage π U T) ↔ ∃ y ∈ F, π y ⤳ x :=
  NoetherianClosedImage.exists_finite_image_generizations π π.continuous
    (residualSource_isClosed U T)

/-- Every residual accumulation point has an actual excluded residual point above a generization. -/
theorem mem_closure_residual_iff (x : X) :
    x ∈ closure (residualBadImage π U T) ↔
      ∃ y : Y, (y ∉ U ∧ y ∉ T) ∧ π y ⤳ x :=
  NoetherianClosedImage.mem_closure_image_iff π π.continuous
    (residualSource_isClosed U T) x

variable [IsProper (T.ι ≫ π)]

/-- At a full fiber, test all residual coordinates over every generization of the retained point. -/
theorem mem_fullFiberInterior_iff_residual_generizations
    (x : X) (hx : x ∈ fullFiberLocus π U) :
    x ∈ fullFiberInterior π U ↔
      ∀ y : Y, π y ⤳ x → y ∉ T → y ∈ U := by
  rw [mem_fullFiberInterior_iff π U T x hx, mem_closure_residual_iff π U T x]
  constructor
  · intro h y hy ht
    by_contra hu
    exact h ⟨y, ⟨hu, ht⟩, hy⟩
  · rintro h ⟨y, ⟨hu, ht⟩, hy⟩
    exact hu (h y hy ht)

/-- One finite family tests the obstruction at every full source fiber simultaneously. -/
theorem exists_finite_fullInterior_test :
    ∃ F : Set Y, F.Finite ∧ (∀ y ∈ F, y ∉ U ∧ y ∉ T) ∧
      ∀ x : X, x ∈ fullFiberLocus π U →
        (x ∈ fullFiberInterior π U ↔ ∀ y ∈ F, ¬ π y ⤳ x) := by
  obtain ⟨F, hF, hFU, ht⟩ := exists_finite_residual_generizations π U T
  refine ⟨F, hF, hFU, fun x hx ↦ ?_⟩
  rw [mem_fullFiberInterior_iff π U T x hx, ht x]
  simp only [not_exists, not_and]

end FLT.Mazur.ProperCoreResidualInterior
