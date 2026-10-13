/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryNormalizationNatural
public import FLT.Mazur.OddWeierstrassSpecialization

/-!
# Normalized coefficient parameters on the odd auxiliary cover

The constructed frame normalization supplies an actual odd-chart parameter.
Its entire equation and coefficient map commute with arbitrary ring pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_three_isUnit)
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original odd-chart coefficient map on any pullback of the auxiliary section ring. -/
def auxiliaryCoefficientHom : OddChartRing →+* R := g.comp auxiliaryCoefficientSections

/-- Three remains invertible over every auxiliary ring pullback. -/
theorem auxiliaryCoefficient_three_isUnit (g : AuxiliarySectionRing →+* R) : IsUnit (3 : R) := by
  simpa only [map_ofNat] using oddChart_three_isUnit.map (auxiliaryCoefficientHom g)

/-- The normalized equation determines its actual coefficient parameter on the odd chart. -/
def auxiliaryNormalizedCoefficientHom : OddChartRing →+* R :=
  specialize (auxiliaryNormalizedEquation g) (auxiliaryCoefficient_three_isUnit g)
    (auxiliaryNormalizedEquation_discriminant g)

/-- The coefficient parameter recovers the entire normalized five-coefficient equation. -/
theorem auxiliaryNormalizedCoefficientHom_equation :
    oddChartEquation.map (auxiliaryNormalizedCoefficientHom g) = auxiliaryNormalizedEquation g :=
  oddChartEquation_specialize _ _ _

/-- The actual normalized coefficient parameter as a morphism of schemes. -/
def auxiliaryNormalizedCoefficientBase : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (auxiliaryNormalizedCoefficientHom g))

/-- Every further ring map retains the constructed normalized coefficient parameter. -/
theorem auxiliaryNormalizedCoefficientHom_natural {S : Type} [CommRing S] (f : R →+* S) :
    f.comp (auxiliaryNormalizedCoefficientHom g) =
      auxiliaryNormalizedCoefficientHom (f.comp g) := by
  unfold auxiliaryNormalizedCoefficientHom
  have he := auxiliaryNormalizedEquation_natural g f
  have hd : IsUnit ((auxiliaryNormalizedEquation g).map f).Δ :=
    he ▸ auxiliaryNormalizedEquation_discriminant (f.comp g)
  rw [specialize_natural _ _ _ f (auxiliaryCoefficient_three_isUnit (f.comp g)) hd]
  congr 1
  exact he.symm

end FLT.Mazur.OddWeierstrassParameter
