/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXStandardPuncture

/-!
# Original initial coordinates on the complete standard puncture

The constructed inverse incidence is invertible on all of D(p), and the
original slope remains in the original nilpotent arithmetic ideal.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "L" => PolynomialNodeOpen W s
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "P" => algebraMap N D (NodalFiber.p s)
local notation "Q" => algebraMap N D (NodalFiber.q s)
local notation "hu" => standardInitialPuncture_denominator_unit W s I hI ha hs
local notation "T" => polynomialNodeInverseT b3 r₀ I hI hm₀ h3 W P Q hu

/-- All original initial functions evaluated on the complete standard puncture. -/
def standardInitialEvaluation : Coordinate W s b3 b4 b6 →ₐ[R] D :=
  polynomialNodeEvaluation W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 P Q hu (by
    rw [← map_mul, NodalFiber.relation, ← IsScalarTower.algebraMap_apply R N D])
local notation "F" => standardInitialEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The original incidence is the full constructed inverse parameter. -/
theorem standardInitialEvaluation_t : F (t W s b3 b4 b6) = T :=
  polynomialNodeEvaluation_t ..

/-- The original slope retains the polynomial root correction on the standard puncture. -/
theorem standardInitialEvaluation_v :
    F (v W s b3 b4 b6) = Q + (r₀).eval₂ (algebraMap R D) T :=
  polynomialNodeEvaluation_v ..

/-- The full small factor is exactly the standard second node coordinate. -/
theorem standardInitialEvaluation_small :
    F (polynomialSmallFactor W s b3 b4 b6 r₀) = Q :=
  polynomialNodeEvaluation_small ..

/-- The full corrected incidence is exactly the standard first node coordinate. -/
theorem standardInitialEvaluation_first :
    F (t W s b3 b4 b6 * polynomialOppositeFactor W s b3 b4 b6 r₀) = P :=
  polynomialNodeEvaluation_first ..

/-- The entire standard puncture has invertible original incidence. -/
theorem standardInitialEvaluation_t_unit : IsUnit (F (t W s b3 b4 b6)) := by
  apply isUnit_of_mul_isUnit_left
    (y := F (polynomialOppositeFactor W s b3 b4 b6 r₀))
  rw [← map_mul, standardInitialEvaluation_first]
  exact IsLocalization.Away.algebraMap_isUnit (NodalFiber.p s)

/-- The original slope on the whole standard puncture retains the small branch label. -/
theorem standardInitialEvaluation_v_mem :
    F (v W s b3 b4 b6) ∈ I.map (algebraMap R D) := by
  rw [standardInitialEvaluation_v]
  exact (I.map (algebraMap R D)).add_mem (standardInitialPuncture_q_mem s I hs)
    (NilpotentPolynomialInverse.eval₂_mem I (algebraMap R D) r₀ hm₀ T)

end FLT.Mazur.WeierstrassModificationX
