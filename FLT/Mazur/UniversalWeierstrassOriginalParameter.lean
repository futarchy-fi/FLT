/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryCartesianOriginalParameter
public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel
public import FLT.Mazur.WeierstrassCoefficientGroup

/-!
# Actual universal parameters for a specified marked Weierstrass family

Specialize the original five universal coefficients to the given equation and
use the proved coefficient group comparison. Returning the complete marking
along that actual comparison gives a morphism to the universal faithful scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (h2 : IsUnit (2 : R)) (hΔ : IsUnit W.Δ)

/-- The original proper cubic group is separated over its coefficient ring. -/
instance originalEquationGroup_separated : IsSeparated (integralCurveGroup W hΔ).X.hom := by
  change IsSeparated (integralCurveStructure W)
  infer_instance

/-- The actual coefficient parameter of the specified original equation. -/
def originalCoefficientBase : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (specialize W h2 hΔ))

/-- The original group is the actual universal group over its coefficient parameter. -/
irreducible_def originalCoefficientGroupIso :
    (Over.pullback (originalCoefficientBase W h2 hΔ)).mapCommGrp.obj
      (integralCurveGroup smoothEquation smoothEquation_discriminant) ≅
        integralCurveGroup W hΔ := by
  letI : Algebra ParameterRing R := (specialize W h2 hΔ).toAlgebra
  have he : W = smoothEquation.map (algebraMap ParameterRing R) :=
    (smoothEquation_specialize W h2 hΔ).symm
  have hd : IsUnit (smoothEquation.map (algebraMap ParameterRing R)).Δ := he ▸ hΔ
  have hg : integralCurveGroup W hΔ =
      integralCurveGroup (smoothEquation.map (algebraMap ParameterRing R)) hd := by
    congr 1
  exact ((eqToIso hg) ≪≫
    integralCurveCoefficientGroupIso smoothEquation smoothEquation_discriminant hd).symm

/-- An actual complete faithful marking gives its original universal parameter. -/
def originalFaithfulParameter (A : Type) [Group A] [Fintype A]
    {U : Over (Spec (.of R))} (f : U ⟶ faithfulScheme (integralCurveGroup W hΔ).X A) :
    (Over.map (originalCoefficientBase W h2 hΔ)).obj U ⟶ faithfulScheme universalGroup A :=
  originalGroupParameter (originalCoefficientBase W h2 hΔ)
    (integralCurveGroup smoothEquation smoothEquation_discriminant)
    (integralCurveGroup W hΔ) (originalCoefficientGroupIso W h2 hΔ) A f

/-- The universal parameter retains every original labeled scheme map after projection. -/
theorem originalFaithfulParameter_value_left (A : Type) [Group A] [Fintype A]
    {U : Over (Spec (.of R))} (f : U ⟶ faithfulScheme (integralCurveGroup W hΔ).X A) (a : A) :
    (originalFaithfulParameter W h2 hΔ A f ≫ faithfulInclusion universalGroup A ≫
      value universalGroup A a).left =
        (f ≫ faithfulInclusion (integralCurveGroup W hΔ).X A ≫
          value (integralCurveGroup W hΔ).X A a).left ≫
            (originalCoefficientGroupIso W h2 hΔ).inv.hom.hom.hom.left ≫
              pullback.fst (integralCurveStructure smoothEquation)
                (originalCoefficientBase W h2 hΔ) := by
  exact (congrArg Over.Hom.left (originalGroupParameter_value
    (originalCoefficientBase W h2 hΔ)
    (integralCurveGroup smoothEquation smoothEquation_discriminant)
    (integralCurveGroup W hΔ) (originalCoefficientGroupIso W h2 hΔ) A f a)).trans
      (originalGroupMarking_left (originalCoefficientBase W h2 hΔ)
        (integralCurveGroup smoothEquation smoothEquation_discriminant)
        (integralCurveGroup W hΔ) (originalCoefficientGroupIso W h2 hΔ) A f a)

end FLT.Mazur.UniversalWeierstrass
