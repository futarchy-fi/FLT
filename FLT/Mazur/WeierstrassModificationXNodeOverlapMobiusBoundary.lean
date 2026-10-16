/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapMobiusUnits
public import FLT.Mazur.WeierstrassModificationXInitialMobiusEquiv
public import FLT.Mazur.NodalFiberTangentMobiusBoundary

/-!
# Both full arithmetic initial-node overlap boundary squares

The actual two original overlap legs factor through the polygon right branch
with their separately constructed full fractional parameters. No reciprocal
identity between these two parameters is assumed away from the zero fiber.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialNodeOverlap W s
local notation "H" => polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3

/-- The exact first fractional parameter on the entire original overlap scheme. -/
def initialMobiusOverlapParameter : Spec (.of O) ⟶ PolygonSmoothing.branchTorus R :=
  Spec.map (CommRingCat.ofHom
    (LaurentUnitPoints.evalUnit (R := R) (polynomialNodeOverlapMobiusUnit W s)).toRingHom)

/-- The exact reflected fractional parameter on the same original overlap scheme. -/
def initialMobiusOverlapOppositeParameter : Spec (.of O) ⟶ PolygonSmoothing.branchTorus R :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
    (polynomialNodeOverlapOppositeMobiusUnit W s b3 b4 b6 r hr I hI hrI h3)).toRingHom)

/-- The first full original overlap leg has its entire arithmetic polygon boundary square. -/
@[reassoc] theorem initialMobiusChart_overlap_first :
    polynomialNodeOverlapInclusion W s ≫ initialMobiusChart W ha s τ hτ =
      initialMobiusOverlapParameter W s ≫ PolygonSmoothing.rightBranchOpen R τ :=
  NodalFiber.tangentMobiusChart_right_boundary s τ (zeroInitialTangentUnit W ha) hτ
    (Algebra.algHom R L O) (polynomialNodeOverlap_fraction_isUnit W s)

/-- The actual opposite original leg has its own complete arithmetic polygon boundary square. -/
@[reassoc] theorem initialMobiusChart_overlap_opposite :
    polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 ≫
      initialMobiusChart W ha s τ hτ =
        initialMobiusOverlapOppositeParameter W s b3 b4 b6 r hr I hI hrI h3 ≫
          PolygonSmoothing.rightBranchOpen R τ := by
  rw [polynomialNodeOverlapOpposite_eq_spec]
  exact NodalFiber.tangentMobiusChart_right_boundary s τ (zeroInitialTangentUnit W ha) hτ
    H (polynomialNodeOverlap_opposite_fraction_isUnit W s b3 b4 b6 r hr I hI hrI h3)

end FLT.Mazur.WeierstrassModificationX
