/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarLocalizedPolynomialDescent

/-!
# Constructing exact equations from separability over localized scalars

Avoidance of the scalar denominators constructs both coefficient maps: into
the full source stalk and into the test residue field. Normalizing the minimal
polynomial gives an actual equation over the original scalar ring. Separability
is tested in the full stalk, not merely in its residue field.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarLocalizedSeparableEquations
open Polynomial
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)

/-- Avoiding scalar denominators construct their action on the unchanged source stalk. -/
def stalkMap : T →+* Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal :=
  IsLocalization.lift (S := T) (M := M)
    (g := (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)).comp σ)
    (fun m ↦ IsLocalization.map_units
      (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (M := (PrimeSpectrum.comap φ Q).asIdeal.primeCompl) ⟨σ m, hM m m.property⟩)

/-- The same avoidance constructs the localized coefficient map to the test residue field. -/
def residueMap : T →+* Q.asIdeal.ResidueField :=
  IsLocalization.lift (S := T) (M := M)
    (g := ((algebraMap B Q.asIdeal.ResidueField).comp φ).comp σ)
    (fun m ↦ isUnit_iff_ne_zero.mpr
      (fun h ↦ hM m m.property (Ideal.algebraMap_residueField_eq_zero.mp h)))

/-- The constructed stalk coefficients restrict to exactly the original scalar map. -/
theorem stalkMap_comp :
    (stalkMap (T := T) M σ φ Q hM).comp (algebraMap R T) =
      (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)).comp σ :=
  IsLocalization.lift_comp _

/-- The constructed residue coefficients restrict to the prescribed test scalar map. -/
theorem residueMap_comp :
    (residueMap (T := T) M σ φ Q hM).comp (algebraMap R T) =
      ((algebraMap B Q.asIdeal.ResidueField).comp φ).comp σ :=
  IsLocalization.lift_comp _

/-- A separable full-stalk element has a constructed equation with exact original coefficients. -/
theorem exists_equation (z : A)
    (hz : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      IsSeparable T
        (algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z)) :
    ∃ F : R[X], ScalarLocalPolynomialTests.Equation σ φ Q z F := by
  let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
  let w := algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal) z
  refine ⟨IsLocalization.integerNormalization M (minpoly T w), ?_⟩
  apply ScalarLocalizedPolynomialDescent.equation_integerNormalization M σ φ Q z
    (minpoly T w) (stalkMap M σ φ Q hM) (residueMap M σ φ Q hM)
    (stalkMap_comp M σ φ Q hM) (residueMap_comp M σ φ Q hM)
  · exact minpoly.aeval T w
  · exact (show (minpoly T w).Separable from hz).map

end FLT.Mazur.ScalarLocalizedSeparableEquations
