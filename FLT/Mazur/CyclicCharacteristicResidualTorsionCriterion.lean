/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUniformResidualDiscrepancy
public import FLT.Mazur.NilpotentTorsionPowerEquality
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Arithmetic control sufficient for the full residual spectrum topology

Nilpotence alone does not identify full and finite invariant spectra. If each
actual discrepancy is additionally killed by a positive integer, a positive
power of every finite fixed function is fully invariant. The actual inclusion
is then integral and induces a homeomorphism. The integer-torsion hypothesis
is an explicit remaining arithmetic obligation, not an instance or an assumption
that the two invariant rings are equal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- A finite invariant with integer-torsion discrepancy has a fully invariant positive power. -/
theorem affineRelabel_pow_mem_residual_of_torsion (s : affineRelabelSections n i)
    {m : ℕ} (hm : 0 < m)
    (hkill : (m : Γ((affineResidualDomain n i).toScheme, ⊤)) *
      ((affineResidualSource n i).appTop s.val -
        (affineResidualTarget n i).appTop s.val) = 0) :
    ∃ e : ℕ, 0 < e ∧ s.val ^ e ∈ affineResidualSections n i := by
  obtain ⟨e, he, h⟩ := NilpotentTorsionPowerEquality.exists_pos_pow_eq hm
    (affineRelabelSections_discrepancy_nilpotent n i s) hkill
  refine ⟨e, he, ?_⟩
  change (affineResidualSource n i).appTop (s.val ^ e) =
    (affineResidualTarget n i).appTop (s.val ^ e)
  simpa only [map_pow] using h

variable (htors : ∀ s : affineRelabelSections n i, ∃ m : ℕ, 0 < m ∧
  (m : Γ((affineResidualDomain n i).toScheme, ⊤)) *
    ((affineResidualSource n i).appTop s.val -
      (affineResidualTarget n i).appTop s.val) = 0)

include htors

/-- Integer-torsion discrepancies put a positive power of every finite invariant in the image. -/
theorem affineResidualToRelabel_power_range (s : affineRelabelSections n i) :
    ∃ e : ℕ, 0 < e ∧ s ^ e ∈ (affineResidualToRelabel n i).range := by
  obtain ⟨m, hm, hkill⟩ := htors s
  obtain ⟨e, he, hs⟩ := affineRelabel_pow_mem_residual_of_torsion n i s hm hkill
  exact ⟨e, he, ⟨⟨s.val ^ e, hs⟩, Subtype.ext rfl⟩⟩

/-- The retained full-to-finite inclusion is integral under the stated arithmetic control. -/
theorem affineResidualToRelabel_isIntegral_of_torsion :
    (affineResidualToRelabel n i).IsIntegral := by
  let _ := (affineResidualToRelabel n i).toAlgebra
  intro s
  obtain ⟨e, he, t, ht⟩ := affineResidualToRelabel_power_range n i htors s
  exact IsIntegral.of_pow he (ht ▸ (affineResidualToRelabel n i).isIntegralElem_map)

/-- Integer-torsion control gives a homeomorphism of the actual full and finite spectra. -/
theorem affineResidualToRelabel_isHomeomorph_of_torsion :
    IsHomeomorph (PrimeSpectrum.comap (affineResidualToRelabel n i)) := by
  apply PrimeSpectrum.isHomeomorph_comap _ (affineResidualToRelabel_power_range n i htors)
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (affineResidualToRelabel_injective n i)]
  exact bot_le

end FLT.Mazur.CyclicCharacteristicOrbit
