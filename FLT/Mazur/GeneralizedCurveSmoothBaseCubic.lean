/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSmoothBaseDimension
public import FLT.Mazur.GeneralizedCurveSmoothIntegral

/-!
# Local cubic coverage on the original smooth base locus

Every generalized curve over a locally Noetherian base has actual pointed
cubic presentations locally on its smooth base locus. The relative dimension
is supplied by the original family; the coefficients and marking equations
come from its actual iterated base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S)

local notation "B" => smoothBaseOpen E
local notation "E'" => baseChange E (Scheme.Opens.ι (B))

/-- The original family on the smooth base locus is geometrically integral. -/
theorem smoothBase_geometricallyIntegral : GeometricallyIntegral (E').curve.hom :=
  smoothCurve_geometricallyIntegral (E')

variable [IsLocallyNoetherian S]

/-- Local cubic coverage of the original smooth locus needs no added dimension assumption. -/
theorem exists_smoothBase_local_pointedCubic
    (s : 𝟙_ (Over S) ⟶ E.curve) {V : (B).toScheme.Opens} {x : (B).toScheme}
    (hx : x ∈ V) :
    ∃ U : (B).toScheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ (W : WeierstrassCurve Γ(U.1.toScheme, ⊤)), W.IsElliptic ∧
        ∃ e : ((E').baseChange U.1.ι).curve.left ≅ integralCurve W,
          e.hom ≫ integralCurveStructure W =
            ((E').baseChange U.1.ι).curve.hom ≫ U.1.toScheme.toSpecΓ ∧
          (pullSection U.1.ι (pullSection (B).ι s)).left ≫ e.hom =
            U.1.toScheme.toSpecΓ ≫ integralCurveZero W :=
  exists_local_pointedCubic (E') (pullSection (B).ι s) hx

end FLT.Mazur.GeneralizedEllipticCurve
