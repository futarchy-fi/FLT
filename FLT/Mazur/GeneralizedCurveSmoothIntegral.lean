/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveLocalCubicPresentation
public import FLT.Mazur.NodalFamilyGeometricConnected
public import FLT.Mazur.SmoothConnectedCurveGeometricIntegral

/-!
# Geometric integrality supplied by the original smooth generalized curve

The original classified family's geometric fibers are connected. For a smooth
relative curve this supplies geometric integrality, so local cubic presentations
need no separate integrality hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart

variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S)

/-- Every original generalized elliptic curve has connected fibers over every field. -/
theorem curve_geometricallyConnected : GeometricallyConnected E.curve.hom :=
  E.family.toNodalFamilyCore.fibers.geometricallyConnected

/-- Smooth original generalized curves are geometrically integral without an added assumption. -/
theorem smoothCurve_geometricallyIntegral [SmoothOfRelativeDimension 1 E.curve.hom] :
    GeometricallyIntegral E.curve.hom := by
  let _ := curve_geometricallyConnected E
  exact smoothConnectedCurve_geometricallyIntegral E.curve.hom

variable [IsLocallyNoetherian S] [SmoothOfRelativeDimension 1 E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.curve) {V : S.Opens} {x : S} (hx : x ∈ V)

include hx in
/-- Every original smooth family has a nonsingular pointed cubic on an affine neighborhood. -/
theorem exists_local_pointedCubic :
    ∃ U : S.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ (W : WeierstrassCurve Γ(U.1.toScheme, ⊤)), W.IsElliptic ∧
        ∃ e : (E.baseChange U.1.ι).curve.left ≅ integralCurve W,
          e.hom ≫ integralCurveStructure W =
            (E.baseChange U.1.ι).curve.hom ≫ U.1.toScheme.toSpecΓ ∧
          (GroupSectionBaseChange.pullSection U.1.ι s).left ≫ e.hom =
            U.1.toScheme.toSpecΓ ≫ integralCurveZero W := by
  let _ := smoothCurve_geometricallyIntegral E
  exact ⟨pointFrameNeighborhood E s hx, mem_pointFrameNeighborhood E s hx,
    pointFrameNeighborhood_le E s hx, pointNeighborhoodEquation E s hx,
    pointNeighborhoodEquation_isElliptic E s hx, pointNeighborhoodCubicIso E s hx,
    pointNeighborhoodCubicIso_over E s hx, pointNeighborhoodCubicIso_marking E s hx⟩

end FLT.Mazur.GeneralizedEllipticCurve
