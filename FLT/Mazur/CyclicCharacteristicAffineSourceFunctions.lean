/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSourceAssembly
public import FLT.Mazur.CyclicCharacteristicAffineSectionReconstruction

/-!
# Full residual functions on the original affine source domain

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
  (j : (invariantAffineCover n (!b)).I₀)

/-- Assemble a residual invariant with its actual opposite reconstruction. -/
def affineSourceFunction (s : affineResidualSections n ⟨!b, j⟩) :
    Γ((affineSourceOpen n b j).toScheme, ⊤) :=
  functionEquiv _ (affineSourceAssemble n b j ((functionEquiv _).symm s.val)
    ((functionEquiv _).symm (affineSectionReconstruction n b j s)))

/-- The selected chart recovers the full residual invariant. -/
theorem affineSourceFunction_selected (s : affineResidualSections n ⟨!b, j⟩) :
    (selectedToAffineSource n b j).appTop (affineSourceFunction n b j s) = s.val := by
  unfold affineSourceFunction
  rw [← functionEquiv_comp, affineSourceAssemble_selected, Equiv.apply_symm_apply]

/-- The opposite chart recovers the actual fppf reconstruction. -/
theorem affineSourceFunction_opposite (s : affineResidualSections n ⟨!b, j⟩) :
    (oppositeToAffineSource n b j).appTop (affineSourceFunction n b j s) =
      affineSectionReconstruction n b j s := by
  unfold affineSourceFunction
  rw [← functionEquiv_comp, affineSourceAssemble_opposite, Equiv.apply_symm_apply]

/-- The two original component pullbacks detect equality of regular functions. -/
theorem affineSourceFunction_ext {s t : Γ((affineSourceOpen n b j).toScheme, ⊤)}
    (hs : (selectedToAffineSource n b j).appTop s =
      (selectedToAffineSource n b j).appTop t)
    (ht : (oppositeToAffineSource n b j).appTop s =
      (oppositeToAffineSource n b j).appTop t) : s = t := by
  apply (functionEquiv _).symm.injective
  have eq_comp {X : Scheme} (f : X ⟶ (affineSourceOpen n b j).toScheme)
      (h : f.appTop s = f.appTop t) :
      f ≫ (functionEquiv _).symm s = f ≫ (functionEquiv _).symm t := by
    apply (functionEquiv _).injective
    simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using h
  exact (affineSourceAssemble_unique n b j _ _ _
    (eq_comp _ hs) (eq_comp _ ht)).trans
      (affineSourceAssemble_unique n b j _ _ _ rfl rfl).symm

/-- Assembly preserves the ring operations on full residual invariants. -/
def affineSourceFunctionHom :
    affineResidualSections n ⟨!b, j⟩ →+* Γ((affineSourceOpen n b j).toScheme, ⊤) where
  toFun := affineSourceFunction n b j
  map_one' := by
    apply affineSourceFunction_ext n b j
    · simp only [affineSourceFunction_selected, OneMemClass.coe_one, map_one]
    · simp only [affineSourceFunction_opposite, map_one]
      exact (affineSectionReconstructionHom n b j).map_one
  map_mul' s t := by
    apply affineSourceFunction_ext n b j
    · simp only [affineSourceFunction_selected, Subring.coe_mul, map_mul]
    · simp only [affineSourceFunction_opposite, map_mul]
      exact (affineSectionReconstructionHom n b j).map_mul s t
  map_zero' := by
    apply affineSourceFunction_ext n b j
    · simp only [affineSourceFunction_selected, ZeroMemClass.coe_zero, map_zero]
    · simp only [affineSourceFunction_opposite, map_zero]
      exact (affineSectionReconstructionHom n b j).map_zero
  map_add' s t := by
    apply affineSourceFunction_ext n b j
    · simp only [affineSourceFunction_selected, Subring.coe_add, map_add]
    · simp only [affineSourceFunction_opposite, map_add]
      exact (affineSectionReconstructionHom n b j).map_add s t

/-- Assembly is injective because the entire selected chart is retained. -/
theorem affineSourceFunction_injective : Function.Injective (affineSourceFunction n b j) := by
  intro s t h
  apply Subtype.ext
  have he := congrArg ((selectedToAffineSource n b j).appTop) h
  simpa only [affineSourceFunction_selected] using he

end FLT.Mazur.CyclicCharacteristicOrbit
