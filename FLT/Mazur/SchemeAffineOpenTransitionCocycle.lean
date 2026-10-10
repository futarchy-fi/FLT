/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOpenTestEvaluation

/-!
# Cocycle for independently restricted pair transitions

Each pair comparison is constructed on its own image intersection. On a
triple subopen all three restrict to a common test, where the already
proved geometric cocycle applies.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open ModuleSheafMorphismGluing ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X}
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (T : Fin 3 → Chart p)
variable [∀ i, ((pullback (T i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (T i).base]
attribute [local irreducible] sheaf imageTestComparison

/-- Comparisons constructed on one common open satisfy the sectionwise cocycle. -/
theorem openTestIso_cocycle (U : X.Opens) (h : ∀ i, U ≤ (T i).base.opensRange)
    (V : X.Opens) (hV : V ≤ U)
    (s : Γ((pushforward (T 0).base).obj ((T 0).sheaf D), V)) :
    localEval ((T 1).openTestIso (T 2) D U (h 1) (h 2)).hom hV
        (localEval ((T 0).openTestIso (T 1) D U (h 0) (h 1)).hom hV s) =
      localEval ((T 0).openTestIso (T 2) D U (h 0) (h 2)).hom hV s := by
  simp only [openTestIso_eval]
  exact imageTestComparison_cocycle_eval D T U.ι
    (fun i ↦ coordinate (T i).base U (h i))
    (fun i ↦ coordinate_comp (T i).base U (h i)) V _ s

/-- The pair-open transitions satisfy the cocycle on every triple subopen. -/
theorem openPairTransition_cocycle (V : X.Opens)
    (h : ∀ i, V ≤ (T i).base.opensRange)
    (s : Γ((pushforward (T 0).base).obj ((T 0).sheaf D), V)) :
    localEval ((T 1).openTestIso (T 2) D
        ((T 1).base.opensRange ⊓ (T 2).base.opensRange) inf_le_left inf_le_right).hom
        (le_inf (h 1) (h 2))
      (localEval ((T 0).openTestIso (T 1) D
        ((T 0).base.opensRange ⊓ (T 1).base.opensRange) inf_le_left inf_le_right).hom
        (le_inf (h 0) (h 1)) s) =
      localEval ((T 0).openTestIso (T 2) D
        ((T 0).base.opensRange ⊓ (T 2).base.opensRange) inf_le_left inf_le_right).hom
        (le_inf (h 0) (h 2)) s := by
  rw [← openTestIso_refine_eval (T 1) (T 2) D _ V _ _ (le_inf (h 1) (h 2)) V le_rfl,
    ← openTestIso_refine_eval (T 0) (T 1) D _ V _ _ (le_inf (h 0) (h 1)) V le_rfl,
    ← openTestIso_refine_eval (T 0) (T 2) D _ V _ _ (le_inf (h 0) (h 2)) V le_rfl]
  exact openTestIso_cocycle D T V h V le_rfl s

end FLT.Mazur.SchemeAffineDescent.Chart
