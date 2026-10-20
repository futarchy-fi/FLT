/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualTorsionCriterion
public import FLT.Mazur.PositiveIntegerLocalization

/-!
# The remaining arithmetic obstruction lives on the rational arrow ring

The exact integer-torsion obligation is equality of finite-invariant pullbacks
after inverting positive integers in the full arrow ring. Reducedness of that
rational ring is a sufficient condition, not a proved property of these charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Integer localization of the full residual arrow ring, retaining its rational nilpotents. -/
abbrev affineResidualRationalArrowRing :=
  PositiveIntegerLocalization.Rationalized Γ((affineResidualDomain n i).toScheme, ⊤)

/-- The arithmetic obstruction is exactly rational vanishing of the actual discrepancy. -/
theorem affineRelabelDiscrepancy_torsion_iff (s : affineRelabelSections n i) :
    (∃ m : ℕ, 0 < m ∧ (m : Γ((affineResidualDomain n i).toScheme, ⊤)) *
      ((affineResidualSource n i).appTop s.val -
        (affineResidualTarget n i).appTop s.val) = 0) ↔
    algebraMap _ (affineResidualRationalArrowRing n i)
      ((affineResidualSource n i).appTop s.val) =
    algebraMap _ (affineResidualRationalArrowRing n i)
      ((affineResidualTarget n i).appTop s.val) :=
  (PositiveIntegerLocalization.map_eq_iff _ _ _).symm

/-- Rational equality suffices for the full-to-finite spectral homeomorphism. -/
theorem affineResidualToRelabel_isHomeomorph_of_rational
    (h : ∀ s : affineRelabelSections n i,
      algebraMap _ (affineResidualRationalArrowRing n i)
        ((affineResidualSource n i).appTop s.val) =
      algebraMap _ (affineResidualRationalArrowRing n i)
        ((affineResidualTarget n i).appTop s.val)) :
    IsHomeomorph (PrimeSpectrum.comap (affineResidualToRelabel n i)) :=
  affineResidualToRelabel_isHomeomorph_of_torsion n i
    (fun s => (affineRelabelDiscrepancy_torsion_iff n i s).mpr (h s))

/-- Reducedness of the rational arrow ring would remove the remaining arithmetic obstruction. -/
theorem affineResidualToRelabel_isHomeomorph_of_rational_reduced
    [IsReduced (affineResidualRationalArrowRing n i)] :
    IsHomeomorph (PrimeSpectrum.comap (affineResidualToRelabel n i)) := by
  apply affineResidualToRelabel_isHomeomorph_of_rational n i
  intro s
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact ((affineRelabelSections_discrepancy_nilpotent n i s).map
    (algebraMap _ (affineResidualRationalArrowRing n i))).eq_zero

end FLT.Mazur.CyclicCharacteristicOrbit
