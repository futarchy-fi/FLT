/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeRootBoundary
public import FLT.Mazur.WeierstrassModificationXFactorRatioLaurentUnit

/-!
# The full opposite factor extends across the retained node

Both constructed roots give a unit on the entire original retained node.
Its actual right restriction is the unchanged full opposite Laurent factor.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "B" => ChartRing π
local notation "J" => I.map (algebraMap R B)
local notation "v" => retainedSlopeRoot W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "r" => retainedConicRoot W π c3 c4 c6 I hI ha h2 h3 h4 h6

/-- The original opposite factor, now constructed on the whole retained node. -/
def retainedOppositeFactor : B := v + (r + retainedSlopeLinear W π c3)
local notation "U" => retainedOppositeFactor W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6

/-- The whole-node opposite factor is a unit with the original tangent reduction. -/
theorem retainedOppositeFactor_isUnit : IsUnit U := by
  have hm : v + r + algebraMap R B c3 * leftCoordinate π ∈ J :=
    (J).add_mem ((J).add_mem (retainedSlopeRoot_mem W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6)
      (retainedConicRoot_mem W π c3 c4 c6 I hI ha h2 h3 h4 h6))
      ((J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3))
  have hu := (NilpotentQuadraticRoot.element_nilpotent J
    (retainedArithmeticIdeal_nilpotent π I hI) hm).isUnit_add_right_of_commute
      (ha.map (algebraMap R B)) (mul_comm _ _)
  convert hu using 1
  unfold retainedOppositeFactor retainedSlopeLinear
  ring

/-- The full correction unit is obtained from the constructed opposite factor. -/
def retainedOppositeUnit : Bˣ :=
  (retainedOppositeFactor_isUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6).unit

/-- The correction unit retains the entire opposite factor, without truncation. -/
theorem retainedOppositeUnit_val :
    (retainedOppositeUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 : B) = U :=
  (retainedOppositeFactor_isUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6).unit_spec

local notation "b3" => π * c3
local notation "b4" => π * c4
local notation "b6" => π ^ 2 * c6
local notation "H3" => I.mul_mem_left π h3
local notation "H4" => I.mul_mem_left π h4
local notation "H6" => I.mul_mem_left (π ^ 2) h6
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 H3 H4 H6
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 H3 H4 H6 false
attribute [local irreducible] retainedSlopeRoot retainedConicRoot polynomialSlopeRoot
  nilpotentLaurentSlope

/-- The regular whole-node unit is exactly the full original opposite factor on the right edge. -/
theorem retainedOppositeFactor_right :
    retainedRightEvaluation π U = E (polynomialOppositeFactor W s b3 b4 b6 r₀) := by
  rw [retainedOppositeFactor, map_add, map_add, retainedSlopeRoot_right,
    retainedConicRoot_right, retainedSlopeLinear_right]
  rw [polynomialOppositeFactor, map_add, hom_polynomial_incidence]
  simp only [laurentBranchEvaluation, laurentSlopeEvaluation_v, laurentSlopeEvaluation_t,
    laurentBranchSlope, Bool.false_eq_true, ↓reduceIte, Polynomial.eval₂_add,
    polynomialSlopeLinear, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rfl

end FLT.Mazur.WeierstrassModificationX
