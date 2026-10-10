/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoefficientGroup
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationNatural

/-!
# The actual coefficient parameter of the normalized auxiliary equation

The original normalized equation supplies its five universal coefficients.
This parameter commutes with arbitrary ring maps and its universal group
pullback is isomorphic to the constructed normalized group scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- Two remains invertible on every auxiliary coefficient ring. -/
theorem auxiliaryCoefficient_two_isUnit (g : AuxiliarySectionRing →+* R) :
    IsUnit (2 : R) := by
  simpa only [map_ofNat] using parameter_two_isUnit.map (auxiliaryCoefficientHom g)

/-- The normalized equation's actual point of the original five-coefficient parameter scheme. -/
def auxiliaryNormalizedCoefficientHom : ParameterRing →+* R :=
  specialize (auxiliaryNormalizedEquation g) (auxiliaryCoefficient_two_isUnit g)
    (auxiliaryNormalizedEquation_discriminant g)

/-- The coefficient parameter recovers the entire normalized equation. -/
theorem auxiliaryNormalizedCoefficientHom_equation :
    smoothEquation.map (auxiliaryNormalizedCoefficientHom g) = auxiliaryNormalizedEquation g :=
  smoothEquation_specialize _ _ _

/-- The actual normalized coefficient parameter as a morphism of schemes. -/
def auxiliaryNormalizedCoefficientBase : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (auxiliaryNormalizedCoefficientHom g))

/-- The normalized coefficient parameter commutes with every change of coefficient ring. -/
theorem auxiliaryNormalizedCoefficientHom_natural {S : Type} [CommRing S] (f : R →+* S) :
    f.comp (auxiliaryNormalizedCoefficientHom g) =
      auxiliaryNormalizedCoefficientHom (f.comp g) := by
  unfold auxiliaryNormalizedCoefficientHom
  have he := auxiliaryNormalizedEquation_natural g f
  have hd : IsUnit ((auxiliaryNormalizedEquation g).map f).Δ :=
    he ▸ auxiliaryNormalizedEquation_discriminant (f.comp g)
  rw [specialize_natural _ _ _ f (auxiliaryCoefficient_two_isUnit (f.comp g)) hd]
  congr 1
  exact he.symm

/-- The original universal group pulled back along the normalized coefficient parameter. -/
def auxiliaryNormalizedUniversalPullbackGroup : CommGrp (Over (Spec (.of R))) :=
  (Over.pullback (auxiliaryNormalizedCoefficientBase g)).mapCommGrp.obj
    (integralCurveGroup smoothEquation smoothEquation_discriminant)

/-- The normalized cubic is the actual universal group over its normalized coefficient parameter. -/
def auxiliaryNormalizedCoefficientGroupIso :
    auxiliaryNormalizedGroup g ≅ auxiliaryNormalizedUniversalPullbackGroup g := by
  letI : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
  have he : auxiliaryNormalizedEquation g = smoothEquation.map (algebraMap ParameterRing R) :=
    (auxiliaryNormalizedCoefficientHom_equation g).symm
  have hd : IsUnit (smoothEquation.map (algebraMap ParameterRing R)).Δ :=
    he ▸ auxiliaryNormalizedEquation_discriminant g
  change integralCurveGroup (auxiliaryNormalizedEquation g) _ ≅ _
  have hg : integralCurveGroup (auxiliaryNormalizedEquation g)
      (auxiliaryNormalizedEquation_discriminant g) =
        integralCurveGroup (smoothEquation.map (algebraMap ParameterRing R)) hd := by
    congr 1
  exact eqToIso hg ≪≫
    integralCurveCoefficientGroupIso smoothEquation smoothEquation_discriminant hd

end FLT.Mazur.UniversalWeierstrass
