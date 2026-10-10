/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarExactness
public import FLT.Mazur.PolygonStageCoefficientKernel

/-!
# The closed-fiber layer of a flat truncated-stage module

For a flat module over R[q]/q^(m+2), multiplication by q^(m+1) identifies
the closed-fiber quotient with the kernel of adjacent reduction. The maps
are explicit and the comparison is natural in linear maps of flat modules.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type*) [CommRing R] (m : ℕ)
  (M : Type*) [AddCommGroup M] [Module (Ring R (m + 1)) M]
  [Module.Flat (Ring R (m + 1)) M]

/-- The last parameter power kills exactly the parameter multiples in a flat module. -/
theorem flat_last_smul_eq_zero_iff (x : M) :
    parameter R (m + 1) ^ (m + 1) • x = 0 ↔ ∃ y, parameter R (m + 1) • y = x :=
  FlatScalarExactness.smul_eq_zero_iff M _ _
    (fun z ↦ (parameter_last_mul_eq_zero_iff R m z).trans
      (reduction_eq_zero_iff R (m + 1) z)) x

/-- The parameter kills exactly the last-power multiples in a flat module. -/
theorem flat_parameter_smul_eq_zero_iff (x : M) :
    parameter R (m + 1) • x = 0 ↔ ∃ y, parameter R (m + 1) ^ (m + 1) • y = x :=
  FlatScalarExactness.smul_eq_zero_iff M _ _
    (fun z ↦ (parameter_mul_eq_zero_iff R m z).trans (restriction_eq_zero_iff R m z)) x

/-- The closed-fiber quotient is the last parameter-power submodule. -/
def closedLayerEquiv :
    (M ⧸ LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
      (parameter R (m + 1)))) ≃ₗ[Ring R (m + 1)]
    LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
      (parameter R (m + 1) ^ (m + 1))) :=
  FlatScalarExactness.quotientEquivRange M _ _
    (fun z ↦ (parameter_last_mul_eq_zero_iff R m z).trans
      (reduction_eq_zero_iff R (m + 1) z))

/-- The actual closed-fiber layer embeds by multiplication with the last parameter power. -/
def closedLayerInclusion :
    (M ⧸ LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
      (parameter R (m + 1)))) →ₗ[Ring R (m + 1)] M :=
  (LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
    (parameter R (m + 1) ^ (m + 1)))).subtype.comp (closedLayerEquiv R m M).toLinearMap

/-- The inclusion has the expected formula on every quotient class. -/
theorem closedLayerInclusion_mk (x : M) :
    closedLayerInclusion R m M (Submodule.Quotient.mk x) =
      parameter R (m + 1) ^ (m + 1) • x := rfl

/-- Flatness makes the closed-fiber layer map injective. -/
theorem closedLayerInclusion_injective : Function.Injective (closedLayerInclusion R m M) :=
  Subtype.val_injective.comp (closedLayerEquiv R m M).injective

/-- The embedded closed fiber is exactly the kernel of adjacent module reduction. -/
theorem closedLayerInclusion_exact :
    Function.Exact (closedLayerInclusion R m M)
      (LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
        (parameter R (m + 1) ^ (m + 1)))).mkQ := by
  intro x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    exact ⟨(closedLayerEquiv R m M).symm ⟨x, hx⟩,
      congrArg Subtype.val ((closedLayerEquiv R m M).apply_symm_apply ⟨x, hx⟩)⟩
  · rintro ⟨y, rfl⟩
    exact (closedLayerEquiv R m M y).property

end FLT.Mazur.PolygonInfinitesimalStages
