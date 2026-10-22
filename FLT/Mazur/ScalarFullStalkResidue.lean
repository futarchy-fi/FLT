/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedSeparableEquations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Residues of arbitrary full source-stalk coordinates

The source stalk maps canonically to the test residue field. This map detects
units, including for fractions which do not come from the original source.
Its restriction to localized scalars is the previously constructed residue map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFullStalkResidue
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  (φ : A →+* B) (Q : PrimeSpectrum B)

/-- The exact full source stalk has a canonical map to the prescribed test residue field. -/
def toResidue : Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal →+*
    Q.asIdeal.ResidueField :=
  (Ideal.ResidueField.map (PrimeSpectrum.comap φ Q).asIdeal Q.asIdeal φ rfl).comp
    (IsLocalRing.residue _)

/-- Source elements have their prescribed residues under the full-stalk map. -/
theorem toResidue_algebraMap (a : A) :
    toResidue φ Q
      (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) a) =
      algebraMap B Q.asIdeal.ResidueField (φ a) :=
  Ideal.ResidueField.map_algebraMap _ _ φ rfl a

/-- A nonzero test residue detects a unit of the full, possibly nonreduced source stalk. -/
theorem toResidue_ne_zero_iff (z : Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) :
    toResidue φ Q z ≠ 0 ↔ IsUnit z := by
  change Ideal.ResidueField.map (PrimeSpectrum.comap φ Q).asIdeal Q.asIdeal φ rfl
    (IsLocalRing.residue (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z) ≠ 0 ↔ _
  rw [map_ne_zero]
  exact IsLocalRing.residue_ne_zero_iff_isUnit z

/-- Nonsingularity can be tested after the residue field extension at the actual test prime. -/
theorem det_isUnit_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)) :
    IsUnit N.det ↔ Matrix.det (N.map (toResidue φ Q)) ≠ 0 := by
  have he := (toResidue φ Q).map_det N
  change toResidue φ Q N.det = Matrix.det (N.map (toResidue φ Q)) at he
  rw [← he, toResidue_ne_zero_iff]

variable [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)
open ScalarLocalizedSeparableEquations

/-- The two constructed coefficient maps agree on the entire scalar localization. -/
theorem toResidue_stalkMap :
    (toResidue φ Q).comp (stalkMap (T := T) M σ φ Q hM) =
      residueMap M σ φ Q hM := by
  apply IsLocalization.ringHom_ext M
  ext r
  change toResidue φ Q ((stalkMap (T := T) M σ φ Q hM).comp (algebraMap R T) r) =
    (residueMap (T := T) M σ φ Q hM).comp (algebraMap R T) r
  rw [stalkMap_comp, residueMap_comp]
  exact toResidue_algebraMap φ Q (σ r)

end FLT.Mazur.ScalarFullStalkResidue
