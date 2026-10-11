/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalAffineCompletion

/-!
# The affine formal comparison over the original power-series base

The actual structure maps of the original stages define the coefficients
on their compatible sections. The completion comparison is an algebra
isomorphism for precisely these coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
  originalStageAffineTransition originalAffineCompletionEquiv

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (exactVeroneseProj K n h).affineOpens)

/-- The original structure maps give a compatible system of complete-base coefficients. -/
theorem originalStageAffineScalars_transition {a b : ℕ} (f : a ⟶ b) (r : PowerSeries K) :
    originalStageAffineTransition K n h f U (originalStageAffineScalars K n h b U r) =
      originalStageAffineScalars K n h a U r := by
  rw [← originalStage_app_scalars, ← originalStage_app_scalars,
    originalStageAffineTransition_app]

/-- Coefficients on formal sections come from the actual original stage structure maps. -/
def originalFormalScalars : PowerSeries K →+* originalAffineFormalSections K n h U where
  toFun r := ⟨fun m ↦ originalStageAffineScalars K n h m U r,
    fun f ↦ originalStageAffineScalars_transition K n h U f r⟩
  map_one' := Subtype.ext (funext fun m ↦ map_one (originalStageAffineScalars K n h m U))
  map_mul' r s := Subtype.ext
    (funext fun m ↦ map_mul (originalStageAffineScalars K n h m U) r s)
  map_zero' := Subtype.ext (funext fun m ↦ map_zero (originalStageAffineScalars K n h m U))
  map_add' r s := Subtype.ext
    (funext fun m ↦ map_add (originalStageAffineScalars K n h m U) r s)

/-- The completion isomorphism retains the actual original power-series algebra structures. -/
def originalAffineCompletionAlgEquiv :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := (originalFormalScalars K n h U).toAlgebra
    AdicCompletion ((compatibleProjAdicIdeal K n h).ideal U)
      Γ(exactVeroneseProj K n h, U) ≃ₐ[PowerSeries K] originalAffineFormalSections K n h U := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := (originalFormalScalars K n h U).toAlgebra
  refine { originalAffineCompletionEquiv K n h U with commutes' := ?_ }
  intro r
  apply Subtype.ext
  funext m
  exact originalAffineCompletionEquiv_scalars K n h U m r

end FLT.Mazur.PolygonInfinitesimalStages
