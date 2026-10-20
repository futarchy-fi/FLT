/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualDegreeTorsion
public import FLT.Mazur.CyclicCharacteristicRelabelCoordinates

/-!
# The full residual spectrum has the finite quotient topology

Degree-power torsion and nilpotence make the original full-to-finite
inclusion integral and a spectral homeomorphism, including in mixed characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- A positive power of every finite fixed function satisfies the full arrow equation. -/
theorem affineRelabelSections_exists_residual_power (s : affineRelabelSections n i) :
    ∃ e : ℕ, 0 < e ∧ s ^ e ∈ (affineResidualToRelabel n i).range :=
  affineResidualToRelabel_power_range n i (affineRelabelSections_discrepancy_torsion n i) s

/-- The actual inclusion of full residual functions into finite invariants is integral. -/
theorem affineResidualToRelabel_isIntegral : (affineResidualToRelabel n i).IsIntegral :=
  affineResidualToRelabel_isIntegral_of_torsion n i
    (affineRelabelSections_discrepancy_torsion n i)

/-- The actual inclusion induces a homeomorphism on spectra. -/
theorem affineResidualToRelabel_isHomeomorph :
    IsHomeomorph (PrimeSpectrum.comap (affineResidualToRelabel n i)) :=
  affineResidualToRelabel_isHomeomorph_of_rational n i
    (affineRelabelSections_rational_condition n i)

/-- The original finite quotient comparison is a homeomorphism onto the full residual spectrum. -/
theorem affineFiniteToResidualSpectrum_isHomeomorph :
    IsHomeomorph (affineFiniteToResidualSpectrum n i) :=
  (affineResidualToRelabel_isHomeomorph n i).comp
    (Scheme.homeoOfIso (affineRelabelSpectrumIso n i)).isHomeomorph

end FLT.Mazur.CyclicCharacteristicOrbit
