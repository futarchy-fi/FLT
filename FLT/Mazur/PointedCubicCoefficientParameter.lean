/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicAuxiliaryCover
public import FLT.Mazur.AuxiliaryCartesianProjectionParameter
public import FLT.Mazur.GroupSchemeBaseChangeComposition

/-!
# Full pointed cubic parameters over the actual universal coefficients

Compose the original canonical spectrum map with the five-coefficient
specialization. The established group comparison and inverse adjunction send
any full faithful marking to the universal parameter scheme on the same test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (h₂ : IsUnit (2 : Γ(S, ⊤)))
local notation "hΔ" => WeierstrassCurve.IsElliptic.isUnit (W := W)
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant

/-- The exact coefficient map from the original base to the universal coefficient scheme. -/
def pointedCubicCoefficientBase : S ⟶ parameterBase :=
  S.toSpecΓ ≫ specializationBase W h₂ hΔ

/-- Bundle the existing original pointed cubic group, without replacing its operations. -/
def pointedCubicCoefficientGroup : CommGrp (Over S) := ⟨(pointedCubicFamily W).group⟩

/-- The original pointed cubic group is the direct pullback through its exact coefficients. -/
irreducible_def pointedCubicCoefficientGroupIso : pointedCubicCoefficientGroup W ≅
    (Over.pullback (pointedCubicCoefficientBase W h₂)).mapCommGrp.obj G :=
  (Over.pullback S.toSpecΓ).mapCommGrp.mapIso (specializationGroupIso W h₂ hΔ) ≪≫
    (GroupSchemeBaseChange.compIso S.toSpecΓ (specializationBase W h₂ hΔ) G).symm

/-- Separatedness is inherited by the original pointed cubic group. -/
local instance : IsSeparated (pointedCubicCoefficientGroup W).X.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (integralCurveStructure W) S.toSpecΓ))

variable (A : Type) [Group A] [Fintype A]

/-- Project all original labels to the actual universal coefficient parameter scheme. -/
def pointedCubicFullCoefficientParameter {U : Over S}
    (f : U ⟶ faithfulScheme (pointedCubicCoefficientGroup W).X A) :
    (Over.map (pointedCubicCoefficientBase W h₂)).obj U ⟶ faithfulScheme (G).X A :=
  cartesianProjectionParameter (pointedCubicCoefficientBase W h₂) G
    (pointedCubicCoefficientGroup W) (pointedCubicCoefficientGroupIso W h₂) A f

/-- The parameter retains the original five coefficients on its original test scheme. -/
@[reassoc] theorem pointedCubicFullCoefficientParameter_base {U : Over S}
    (f : U ⟶ faithfulScheme (pointedCubicCoefficientGroup W).X A) :
    (pointedCubicFullCoefficientParameter W h₂ A f).left ≫ (faithfulScheme (G).X A).hom =
      U.hom ≫ S.toSpecΓ ≫ specializationBase W h₂ hΔ := by
  exact (pointedCubicFullCoefficientParameter W h₂ A f).w

/-- Every full label retains its original group image and direct coefficient projection. -/
theorem pointedCubicFullCoefficientParameter_value {U : Over S}
    (f : U ⟶ faithfulScheme (pointedCubicCoefficientGroup W).X A) (a : A) :
    (pointedCubicFullCoefficientParameter W h₂ A f ≫ faithfulInclusion (G).X A ≫
      value (G).X A a).left =
        (f ≫ faithfulInclusion (pointedCubicCoefficientGroup W).X A ≫
          value (pointedCubicCoefficientGroup W).X A a).left ≫
            (pointedCubicCoefficientGroupIso W h₂).hom.hom.hom.hom.left ≫
              pullback.fst (G).X.hom (pointedCubicCoefficientBase W h₂) :=
  cartesianProjectionParameter_value_left (pointedCubicCoefficientBase W h₂) G
    (pointedCubicCoefficientGroup W) (pointedCubicCoefficientGroupIso W h₂) A f a

end FLT.Mazur.GeneralizedEllipticCurve
