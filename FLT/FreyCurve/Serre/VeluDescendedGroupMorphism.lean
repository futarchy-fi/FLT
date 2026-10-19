/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDescendedDegree
public import FLT.Mazur.ProperRelativePointedGroupHom
public import FLT.Mazur.WeierstrassGeometricIntegral
public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# The descended Vélu map preserves the original rational group laws

The actual descended map preserves infinity. Relative pointed rigidity on the
original proper smooth cubic identifies its multiplication with the existing
target multiplication; the carrier and target equation are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [CharZero K] [CharZero L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] [DecidableEq L]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup (E.map (algebraMap K L)).toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  (V : WeierstrassCurve K)
  (hV : V.map (algebraMap K L) = curve (E.map (algebraMap K L)) G)
  (hG : ∀ (g : L ≃ₐ[K] L) P, P ∈ G →
    Affine.Point.map (W' := E.toAffine) g.toAlgHom P ∈ G)

local notation "SG" => integralCurveGroup E IsElliptic.isUnit
local notation "TG" => integralCurveGroup V
  (IsElliptic.isUnit (self := veluDescendedTarget_isElliptic E G hodd V hV))

/-- The actual descended map bundled over its original coefficient field. -/
def veluDescendedOverMorphism : (SG).X ⟶ (TG).X :=
  Over.homMk (veluDescendedMorphism E G hodd V hV hG)
    (veluDescendedMorphism_base E G hodd V hV hG)

/-- The retained infinity section is the identity of the original group object. -/
theorem veluDescendedOverMorphism_one :
    η[(SG).X] ≫ veluDescendedOverMorphism E G hodd V hV hG = η[(TG).X] := by
  apply Over.OverMorphism.ext
  exact veluDescendedMorphism_zero E G hodd V hV hG

/-- The actual descended map respects the existing scheme group structures. -/
instance veluDescendedOverMorphism_isMonHom :
    IsMonHom (veluDescendedOverMorphism E G hodd V hV hG) := by
  let _ : IsProper (SG).X.hom :=
    inferInstanceAs (IsProper (integralCurveStructure E))
  let _ : IsSeparated (TG).X.hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure V))
  let _ : LocallyOfFiniteType (TG).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (integralCurveStructure V))
  let _ : GeometricallyIntegral (SG).X.hom :=
    inferInstanceAs (GeometricallyIntegral (integralCurveStructure E))
  let _ : SmoothOfRelativeDimension 1 (SG).X.hom :=
    integralCurveStructure_smooth_dimension E IsElliptic.isUnit
  exact FLT.Mazur.FCurve.properRelative_isMonHom_of_one _ _ _
    (veluDescendedOverMorphism_one E G hodd V hV hG)

/-- Multiplication compatibility is equality of the original scheme morphisms. -/
@[reassoc] theorem veluDescendedMorphism_multiplication :
    integralCurveAddition E IsElliptic.isUnit ≫ veluDescendedMorphism E G hodd V hV hG =
      (veluDescendedOverMorphism E G hodd V hV hG ⊗ₘ
        veluDescendedOverMorphism E G hodd V hV hG).left ≫
          integralCurveAddition V (veluDescendedTarget_isElliptic E G hodd V hV).isUnit :=
  congrArg Over.Hom.left (IsMonHom.mul_hom (veluDescendedOverMorphism E G hodd V hV hG))

/-- The rational group homomorphism retains exactly the constructed descended morphism. -/
def veluDescendedGroupHom : SG ⟶ TG := ⟨⟨⟨veluDescendedOverMorphism E G hodd V hV hG⟩⟩⟩

/-- Forgetting the bundled group homomorphism recovers the original scheme map. -/
theorem veluDescendedGroupHom_left :
    (veluDescendedGroupHom E G hodd V hV hG).hom.hom.hom.left =
      veluDescendedMorphism E G hodd V hV hG := rfl

end WeierstrassCurve.Velu
