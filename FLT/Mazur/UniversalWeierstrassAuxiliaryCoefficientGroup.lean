/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationGroup
public import FLT.Mazur.WeierstrassCoefficientGroup

/-!
# The actual auxiliary cubic is the base-changed universal group scheme

The coefficient map obtained from auxiliary global functions gives the
original auxiliary equation. The proved coefficient comparison identifies
its complete group object with the actual pullback of the universal group.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The original coefficient homomorphism of an auxiliary ring-valued point. -/
def auxiliaryCoefficientHom : ParameterRing →+* R := g.comp auxiliaryCoefficientSections

/-- The pulled-back auxiliary equation is exactly the coefficient specialization. -/
theorem auxiliaryPullbackEquation_coefficient :
    auxiliaryPullbackEquation g = smoothEquation.map (auxiliaryCoefficientHom g) := by
  rw [auxiliaryPullbackEquation, auxiliarySectionEquation, WeierstrassCurve.map_map]
  rfl

/-- The actual coefficient morphism of the auxiliary ring-valued point. -/
def auxiliaryCoefficientBase : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (auxiliaryCoefficientHom g))

/-- The actual pullback of the original universal commutative group scheme. -/
def auxiliaryUniversalPullbackGroup : CommGrp (Over (Spec (.of R))) :=
  (Over.pullback (auxiliaryCoefficientBase g)).mapCommGrp.obj
    (integralCurveGroup smoothEquation smoothEquation_discriminant)

/-- The actual auxiliary cubic is the original universal group after coefficient base change. -/
def auxiliaryCoefficientGroupIso :
    auxiliaryPullbackGroup g ≅ auxiliaryUniversalPullbackGroup g := by
  letI : Algebra ParameterRing R := (auxiliaryCoefficientHom g).toAlgebra
  have he : auxiliaryPullbackEquation g = smoothEquation.map (algebraMap ParameterRing R) :=
    auxiliaryPullbackEquation_coefficient g
  have hd : IsUnit (smoothEquation.map (algebraMap ParameterRing R)).Δ :=
    he ▸ auxiliaryPullbackEquation_discriminant g
  change integralCurveGroup (auxiliaryPullbackEquation g) _ ≅ _
  have hg : integralCurveGroup (auxiliaryPullbackEquation g)
      (auxiliaryPullbackEquation_discriminant g) =
        integralCurveGroup (smoothEquation.map (algebraMap ParameterRing R)) hd := by
    congr 1
  exact eqToIso hg ≪≫
    integralCurveCoefficientGroupIso smoothEquation smoothEquation_discriminant hd

end FLT.Mazur.UniversalWeierstrass
