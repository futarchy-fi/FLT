/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicIntegerSourceAssembly
public import FLT.Mazur.CyclicCharacteristicResidualSectionReconstruction

/-!
# Residual functions on the original characteristic source open

A full residual invariant and its opposite fppf reconstruction assemble into
an actual regular function on the original source open. Both original chart
pullbacks are retained, and together determine the assembled function.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- Assemble a residual invariant with its actual opposite reconstruction. -/
def integerSourceFunction (s : chartResidualSections n (!b)) :
    Γ((integerSourceOpen n b).toScheme, ⊤) :=
  functionEquiv _ (integerSourceAssemble n b ((functionEquiv _).symm s.val)
    ((functionEquiv _).symm (residualSectionReconstruction n b s)))

/-- The selected chart recovers the full residual invariant. -/
theorem integerSourceFunction_selected (s : chartResidualSections n (!b)) :
    (selectedToIntegerSource n b).appTop (integerSourceFunction n b s) = s.val := by
  unfold integerSourceFunction
  rw [← functionEquiv_comp, integerSourceAssemble_selected, Equiv.apply_symm_apply]

/-- The opposite chart recovers the actual fppf reconstruction. -/
theorem integerSourceFunction_opposite (s : chartResidualSections n (!b)) :
    (oppositeToIntegerSource n b).appTop (integerSourceFunction n b s) =
      residualSectionReconstruction n b s := by
  unfold integerSourceFunction
  rw [← functionEquiv_comp, integerSourceAssemble_opposite, Equiv.apply_symm_apply]

/-- The two original component pullbacks detect equality of regular functions. -/
theorem integerSourceFunction_ext {s t : Γ((integerSourceOpen n b).toScheme, ⊤)}
    (hs : (selectedToIntegerSource n b).appTop s =
      (selectedToIntegerSource n b).appTop t)
    (ht : (oppositeToIntegerSource n b).appTop s =
      (oppositeToIntegerSource n b).appTop t) : s = t := by
  apply (functionEquiv _).symm.injective
  have eq_comp {X : Scheme} (f : X ⟶ (integerSourceOpen n b).toScheme)
      (h : f.appTop s = f.appTop t) :
      f ≫ (functionEquiv _).symm s = f ≫ (functionEquiv _).symm t := by
    apply (functionEquiv _).injective
    simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using h
  exact (integerSourceAssemble_unique n b _ _ _
    (eq_comp _ hs) (eq_comp _ ht)).trans
      (integerSourceAssemble_unique n b _ _ _ rfl rfl).symm

/-- Assembly preserves the ring operations on full residual invariants. -/
def integerSourceFunctionHom :
    chartResidualSections n (!b) →+* Γ((integerSourceOpen n b).toScheme, ⊤) where
  toFun := integerSourceFunction n b
  map_one' := by
    apply integerSourceFunction_ext n b
    · simp only [integerSourceFunction_selected, OneMemClass.coe_one, map_one]
    · simp only [integerSourceFunction_opposite, map_one]
      exact (residualSectionReconstructionHom n b).map_one
  map_mul' s t := by
    apply integerSourceFunction_ext n b
    · simp only [integerSourceFunction_selected, Subring.coe_mul, map_mul]
    · simp only [integerSourceFunction_opposite, map_mul]
      exact (residualSectionReconstructionHom n b).map_mul s t
  map_zero' := by
    apply integerSourceFunction_ext n b
    · simp only [integerSourceFunction_selected, ZeroMemClass.coe_zero, map_zero]
    · simp only [integerSourceFunction_opposite, map_zero]
      exact (residualSectionReconstructionHom n b).map_zero
  map_add' s t := by
    apply integerSourceFunction_ext n b
    · simp only [integerSourceFunction_selected, Subring.coe_add, map_add]
    · simp only [integerSourceFunction_opposite, map_add]
      exact (residualSectionReconstructionHom n b).map_add s t

/-- Assembly is injective because the entire selected chart is retained. -/
theorem integerSourceFunction_injective : Function.Injective (integerSourceFunction n b) := by
  intro s t h
  apply Subtype.ext
  have he := congrArg ((selectedToIntegerSource n b).appTop) h
  simpa only [integerSourceFunction_selected] using he

end FLT.Mazur.CyclicCharacteristicOrbit
