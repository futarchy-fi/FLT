/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineInvariantReconstruction
public import FLT.Mazur.CyclicCharacteristicAffineSectionTransport

/-!
# Actual affine-domain sections equal the full residual invariant ring

Reconstruction on the original source is inverse to the actual locally ringed
pullback from the affine orbit open. This is a comparison of the full section
rings; scheme effectivity still requires spectrum topology and stalk comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)
  (j : (invariantAffineCover n (!b)).I₀)

/-- The actual source pullback is the assembly of its selected full residual value. -/
theorem affineSourceInvariantSectionMap_assembly
    (s : (invariantSheaf n).obj.obj (op (affineOrbitOpen n ⟨!b, j⟩))) :
    affineSourceInvariantSectionMap n b j s =
      affineSourceFunction n b j (affineResidualSectionMap n ⟨!b, j⟩ s) := by
  apply affineSourceFunction_ext n b j
  · rw [affineSourceFunction_selected, affineResidualSectionMap_val]
    exact congrArg (fun f => f s) (affineSourceInvariantSectionMap_selected n b j)
  · rw [affineSourceFunction_opposite]
    exact affineSourceInvariantSectionMap_opposite n b j s

/-- Reconstruction retains the entire original source regular function. -/
theorem affineInvariantReconstruction_source (s : affineResidualSections n ⟨!b, j⟩) :
    affineSourceInvariantSectionMap n b j (affineInvariantReconstruction n b j s) =
      affineSourceFunction n b j s := by
  rw [affineSourceInvariantSectionMap_inclusion, CommRingCat.comp_apply,
    affineInvariantReconstruction_inclusion]
  exact (affineSourceOpen n b j).topIso.hom_inv_id_apply _

/-- Pulling a reconstructed section back to the affine chart recovers the initial invariant. -/
theorem affineInvariantReconstruction_right_inv (s : affineResidualSections n ⟨!b, j⟩) :
    affineResidualSectionMap n ⟨!b, j⟩ (affineInvariantReconstruction n b j s) = s := by
  apply Subtype.ext
  rw [affineResidualSectionMap_val, ← affineSourceInvariantSectionMap_selected,
    CommRingCat.comp_apply, affineInvariantReconstruction_source, affineSourceFunction_selected]

/-- Reconstructing an actual section from its full residual pullback recovers that section. -/
theorem affineInvariantReconstruction_left_inv
    (s : (invariantSheaf n).obj.obj (op (affineOrbitOpen n ⟨!b, j⟩))) :
    affineInvariantReconstruction n b j (affineResidualSectionMap n ⟨!b, j⟩ s) = s := by
  apply affineSourceInvariantSectionMap_injective n b j
  rw [affineInvariantReconstruction_source, affineSourceInvariantSectionMap_assembly]

/-- The genuine comparison is bijective on every selected saturated affine domain. -/
theorem affineResidualSectionMap_bijective (i : InvariantAffineIndex n) :
    Function.Bijective (affineResidualSectionMap n i) := by
  rcases i with ⟨c, k⟩
  cases c
  · exact ⟨Function.LeftInverse.injective (affineInvariantReconstruction_left_inv n true k),
      Function.RightInverse.surjective (affineInvariantReconstruction_right_inv n true k)⟩
  · exact ⟨Function.LeftInverse.injective (affineInvariantReconstruction_left_inv n false k),
      Function.RightInverse.surjective (affineInvariantReconstruction_right_inv n false k)⟩

/-- Actual sections on the quotient open are exactly its full affine residual invariants. -/
def affineResidualSectionsEquiv (i : InvariantAffineIndex n) :
    (invariantSheaf n).obj.obj (op (affineOrbitOpen n i)) ≃+* affineResidualSections n i :=
  RingEquiv.ofBijective (affineResidualSectionMap n i) (affineResidualSectionMap_bijective n i)

/-- The ring equivalence is the actual locally ringed pullback constructed earlier. -/
theorem affineResidualSectionsEquiv_apply (i : InvariantAffineIndex n)
    (s : (invariantSheaf n).obj.obj (op (affineOrbitOpen n i))) :
    affineResidualSectionsEquiv n i s = affineResidualSectionMap n i s := rfl

end FLT.Mazur.CyclicCharacteristicOrbit
