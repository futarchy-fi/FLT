/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialMobiusEquiv
public import FLT.Mazur.WeierstrassModificationXLaurentNodeParameter
public import FLT.Mazur.NodalFiberTangentMobiusBoundary

/-!
# The full original arithmetic Laurent boundary of the fractional initial chart

The retained parameter is the inverse original Laurent coordinate multiplied
by the full opposite-factor correction, divided by the tangent unit, plus the
normalized smoothing. Nilpotence proves that this entire parameter is a unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "a" => zeroInitialTangentUnit W ha
local notation "B" => R[T;T⁻¹]
local notation "L" => PolynomialNodeOpen W s
local notation "N" => NodalFiber.Coordinate s
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "P" => algebraMap N L (NodalFiber.p s)
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 false
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6

include ha hτ hs hI in
/-- The original nilpotent arithmetic scale remains nilpotent after tangent normalization. -/
theorem initialMobius_smoothing_nilpotent : IsNilpotent τ := by
  apply ((ha.pow 2).isNilpotent_unit_mul_of_commute_iff (mul_comm _ _)).mp
  rw [← hτ]
  exact NilpotentQuadraticRoot.element_nilpotent I hI hs

include hτ in
/-- The actual translated first fractional boundary coordinate is a unit at every order. -/
theorem initialMobiusLaurent_isUnit :
    IsUnit (algebraMap R B (↑a⁻¹ : R) * G P + algebraMap R B τ) := by
  have hn := (initialMobius_smoothing_nilpotent W ha s τ hτ I hI hs).map
    (algebraMap R B)
  apply hn.isUnit_add_left_of_commute
  · exact (a⁻¹.isUnit.map (algebraMap R B)).mul
      (laurentNodeRestriction_p_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
  · exact mul_comm _ _

/-- The exact original retained Laurent parameter after full fractional normalization. -/
def initialMobiusLaurentUnit : Bˣ :=
  (initialMobiusLaurent_isUnit W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6).unit

/-- Every opposite-factor correction and the translated smoothing survive in this unit. -/
theorem initialMobiusLaurentUnit_coe :
    (initialMobiusLaurentUnit W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6 : B) =
      algebraMap R B (↑a⁻¹ : R) *
        (LaurentPolynomial.T (-1) * E (polynomialOppositeFactor W s b3 b4 b6 r₀)) +
          algebraMap R B τ := by
  rw [initialMobiusLaurentUnit, IsUnit.unit_spec, laurentNodeRestriction_p]

/-- The actual original full Laurent restriction commutes with the fractional polygon chart. -/
@[reassoc] theorem initialMobiusChart_laurent_boundary :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫ initialMobiusChart W ha s τ hτ =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
        (initialMobiusLaurentUnit W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6)).toRingHom) ≫
          PolygonSmoothing.leftBranchOpen R τ :=
  NodalFiber.tangentMobiusChart_left_boundary s τ a hτ G
    (initialMobiusLaurent_isUnit W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
