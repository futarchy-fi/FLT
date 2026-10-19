/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicIntegerInvariantReconstruction
public import FLT.Mazur.CyclicCharacteristicIntegerSectionTransport

/-!
# Actual characteristic invariant sections equal full residual invariants

Reconstruction on the original source is inverse to the actual locally ringed
chart pullback. Hence the characteristic invariant sheaf and both the normalized
and finite quotient residual equalizers have isomorphic section rings.
No affineness or coarse scheme representability is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The actual source section pullback is the assembly of the selected residual value. -/
theorem integerSourceInvariantSectionMap_assembly
    (s : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger (!b))))) :
    integerSourceInvariantSectionMap n b s =
      integerSourceFunction n b (chartResidualSectionMap n (!b) s) := by
  apply integerSourceFunction_ext n b
  · rw [integerSourceFunction_selected, chartResidualSectionMap_val]
    exact congrArg (fun f => f s) (integerSourceInvariantSectionMap_selected n b)
  · rw [integerSourceFunction_opposite,
      ← oppositeInvariantSectionMap_reconstruction]
    exact congrArg (fun f => f s) (integerSourceInvariantSectionMap_opposite n b)

/-- Reconstruction retains the entire original source regular function. -/
theorem integerInvariantReconstruction_source (s : chartResidualSections n (!b)) :
    integerSourceInvariantSectionMap n b (integerInvariantReconstruction n b s) =
      integerSourceFunction n b s := by
  rw [integerSourceInvariantSectionMap_inclusion, CommRingCat.comp_apply,
    integerInvariantReconstruction_inclusion]
  exact (integerSourceOpen n b).topIso.hom_inv_id_apply _

/-- Pulling the reconstructed section back to the selected chart gives the initial invariant. -/
theorem integerInvariantReconstruction_right_inv (s : chartResidualSections n (!b)) :
    chartResidualSectionMap n (!b) (integerInvariantReconstruction n b s) = s := by
  apply Subtype.ext
  rw [chartResidualSectionMap_val,
    ← integerSourceInvariantSectionMap_selected, CommRingCat.comp_apply,
    integerInvariantReconstruction_source, integerSourceFunction_selected]

/-- Reconstruction of an actual invariant section recovers that section itself. -/
theorem integerInvariantReconstruction_left_inv
    (s : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger (!b))))) :
    integerInvariantReconstruction n b (chartResidualSectionMap n (!b) s) = s := by
  apply integerSourceInvariantSectionMap_injective n b
  rw [integerInvariantReconstruction_source, integerSourceInvariantSectionMap_assembly]

/-- The actual chart section comparison is bijective for either characteristic. -/
theorem chartResidualSectionMap_bijective : Function.Bijective (chartResidualSectionMap n b) := by
  have h : Function.Bijective (chartResidualSectionMap n (!(!b))) :=
    ⟨Function.LeftInverse.injective (integerInvariantReconstruction_left_inv n (!b)),
      Function.RightInverse.surjective (integerInvariantReconstruction_right_inv n (!b))⟩
  cases b <;> exact h

/-- Sections on the characteristic orbit open are exactly full normalized residual invariants. -/
def chartResidualSectionsEquiv :
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b))) ≃+*
      chartResidualSections n b :=
  RingEquiv.ofBijective (chartResidualSectionMap n b) (chartResidualSectionMap_bijective n b)

/-- The ring equivalence retains the actual locally ringed pullback. -/
theorem chartResidualSectionsEquiv_apply
    (s : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b)))) :
    chartResidualSectionsEquiv n b s = chartResidualSectionMap n b s := rfl

/-- The same actual section ring is the full residual invariant ring of the finite quotient. -/
def finiteInvariantSectionsEquiv :
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b))) ≃+*
      finiteResidualSections n b :=
  (chartResidualSectionsEquiv n b).trans (finiteResidualSectionsEquiv n b).symm

/-- This equivalence is the previously constructed finite-quotient section comparison. -/
theorem finiteInvariantSectionsEquiv_apply
    (s : (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger b)))) :
    finiteInvariantSectionsEquiv n b s = finiteInvariantSectionMap n b s := rfl

end FLT.Mazur.CyclicCharacteristicOrbit
