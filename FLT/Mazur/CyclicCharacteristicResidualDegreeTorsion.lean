/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvertibleResidual
public import FLT.Mazur.CyclicCharacteristicRationalResidualCriterion
public import FLT.Mazur.SchemeNaturalUnitSectionTorsion

/-!
# Actual finite-invariant discrepancies are degree-power torsion

Apply exact invertible-level descent on the original arrow scheme's degree
principal open. Quasi-compactness supplies an annihilating degree power,
which proves the rational equality without discarding nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Every discrepancy is killed by a power of the actual level in the original arrow ring. -/
theorem affineRelabelSections_discrepancy_degree_torsion (s : affineRelabelSections n i) :
    ∃ k : ℕ, (n : Γ((affineResidualDomain n i).toScheme, ⊤)) ^ k *
      ((affineResidualSource n i).appTop s.val -
        (affineResidualTarget n i).appTop s.val) = 0 := by
  apply SchemeNaturalUnitLocus.exists_pow_mul_eq_zero
  rw [map_sub, sub_eq_zero]
  exact affineRelabelSections_invertible_condition n i s _
    (SchemeNaturalUnitLocus.isUnit _ n)

/-- The exact arithmetic obligation holds for every actual finite invariant. -/
theorem affineRelabelSections_discrepancy_torsion (s : affineRelabelSections n i) :
    ∃ m : ℕ, 0 < m ∧ (m : Γ((affineResidualDomain n i).toScheme, ⊤)) *
      ((affineResidualSource n i).appTop s.val -
        (affineResidualTarget n i).appTop s.val) = 0 := by
  obtain ⟨k, hk⟩ := affineRelabelSections_discrepancy_degree_torsion n i s
  exact ⟨n ^ k, pow_pos (Nat.pos_of_ne_zero (NeZero.ne n)) _, by
    simpa only [Nat.cast_pow] using hk⟩

/-- Both full arrow pullbacks agree in the original rationalized arrow ring. -/
theorem affineRelabelSections_rational_condition (s : affineRelabelSections n i) :
    algebraMap _ (affineResidualRationalArrowRing n i)
      ((affineResidualSource n i).appTop s.val) =
    algebraMap _ (affineResidualRationalArrowRing n i)
      ((affineResidualTarget n i).appTop s.val) :=
  (affineRelabelDiscrepancy_torsion_iff n i s).mp
    (affineRelabelSections_discrepancy_torsion n i s)

end FLT.Mazur.CyclicCharacteristicOrbit
