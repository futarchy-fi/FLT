/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentRelations
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# A secant and reversed-tangent cover of the tangent source

The original tangent denominator is the reversed denominator minus a multiple
of the divided abscissa difference. Since it is a unit, the other two
principal opens cover the entire tangent source, over every base ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c

/-- The two coefficients whose principal opens cover the original tangent chart. -/
def dividedTangentReverseCoverElement (b : Bool) : T :=
  algebraMap S T (if b then dividedTangentDenominator W s b3 b4 b6 c a
    else a (x W s b3 b4 b6) - c (x W s b3 b4 b6))

/-- The two coefficients generate the unit ideal, with no regularity hypothesis. -/
theorem dividedTangentReverseCover_span :
    Ideal.span (Set.range (dividedTangentReverseCoverElement W s b3 b4 b6 a c)) = ⊤ := by
  let I := Ideal.span (Set.range (dividedTangentReverseCoverElement W s b3 b4 b6 a c))
  have hx : dividedTangentReverseCoverElement W s b3 b4 b6 a c false ∈ I :=
    Ideal.subset_span ⟨false, rfl⟩
  have hd : dividedTangentReverseCoverElement W s b3 b4 b6 a c true ∈ I :=
    Ideal.subset_span ⟨true, rfl⟩
  have he : algebraMap S T (dividedTangentDenominator W s b3 b4 b6 a c) =
      dividedTangentReverseCoverElement W s b3 b4 b6 a c true -
        algebraMap R T W.a₁ * dividedTangentReverseCoverElement W s b3 b4 b6 a c false := by
    simp only [dividedTangentReverseCoverElement, dividedTangentDenominator,
      Bool.false_eq_true, ite_true, ite_false, map_add, map_sub, map_mul,
      ← IsScalarTower.algebraMap_apply R S T]
    ring
  have hm : algebraMap S T (dividedTangentDenominator W s b3 b4 b6 a c) ∈ I := by
    rw [he]
    exact I.sub_mem hd (I.mul_mem_left _ hx)
  exact Ideal.eq_top_of_isUnit_mem I hm (IsLocalization.Away.algebraMap_isUnit (S := T) _)

/-- The actual two-member affine open cover, ready to pull back along any test scheme. -/
def dividedTangentReverseCover : (Spec (.of T)).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop
    (dividedTangentReverseCoverElement W s b3 b4 b6 a c)
    (dividedTangentReverseCover_span W s b3 b4 b6 a c)

end FLT.Mazur.WeierstrassDilatation
