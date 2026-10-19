/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalPointValues
public import FLT.FreyCurve.Serre.VeluElliptic
public import FLT.Mazur.ProperGroupPointedHom
public import FLT.Mazur.WeierstrassGeometricIntegral
public import FLT.Mazur.WeierstrassIntegralGroup
public import FLT.Mazur.WeierstrassIntegralProper
public import FLT.Mazur.WeierstrassIntegralSmooth

/-!
# The global Vélu morphism preserves the original scheme group laws

The proved ellipticity of the exact target supplies its existing cubic group
law. Pointed rigidity on the proper integral source proves multiplication
compatibility for the actual global morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

local notation "SG" => integralCurveGroup E IsElliptic.isUnit
local notation "TG" => integralCurveGroup (curve E G)
  (IsElliptic.isUnit (self := curve_isElliptic E G hodd))

/-- The actual global Vélu morphism bundled over the original coefficient field. -/
def veluGlobalOverMorphism : (SG).X ⟶ (TG).X :=
  Over.homMk (veluGlobalMorphism E G hodd) (veluGlobalMorphism_base E G hodd)

/-- Its original infinity comparison is the identity law of the original scheme groups. -/
theorem veluGlobalOverMorphism_one :
    η[(SG).X] ≫ veluGlobalOverMorphism E G hodd =
      η[(TG).X] := by
  apply Over.OverMorphism.ext
  exact veluGlobalMorphism_zero E G hodd

/-- The actual global Vélu morphism preserves the existing source and target group laws. -/
instance veluGlobalOverMorphism_isMonHom : IsMonHom (veluGlobalOverMorphism E G hodd) := by
  let _ : IsProper (SG).X.hom :=
    inferInstanceAs (IsProper (integralCurveStructure E))
  let _ : IsSeparated (TG).X.hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure (curve E G)))
  let _ : LocallyOfFiniteType (TG).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (integralCurveStructure (curve E G)))
  let _ := LocallyOfFiniteType.isLocallyNoetherian (integralCurveStructure E)
  let _ := integralCurveStructure_smooth_dimension E IsElliptic.isUnit
  let _ : IsIntegral ((SG).X ⊗ (SG).X).left := by
    change IsIntegral (Limits.pullback (integralCurveStructure E) (integralCurveStructure E))
    infer_instance
  exact properGroup_isMonHom_of_one _ _ _ (veluGlobalOverMorphism_one E G hodd)

/-- Multiplication compatibility holds as equality of the original actual scheme morphisms. -/
@[reassoc] theorem veluGlobalMorphism_multiplication :
    integralCurveAddition E IsElliptic.isUnit ≫ veluGlobalMorphism E G hodd =
      (veluGlobalOverMorphism E G hodd ⊗ₘ veluGlobalOverMorphism E G hodd).left ≫
        integralCurveAddition (curve E G) (curve_isElliptic E G hodd).isUnit :=
  congrArg Over.Hom.left (IsMonHom.mul_hom (veluGlobalOverMorphism E G hodd))

end WeierstrassCurve.Velu
