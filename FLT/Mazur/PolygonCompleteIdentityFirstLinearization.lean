/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentSquareZeroLinearization
public import FLT.Mazur.PolygonCompleteIdentityFirstCorrection

/-!
# An explicit first-order coordinate bijection for the original identity law

The canonical correction gives an actual bijection on every coefficient
algebra's unit points, intertwining the original first-stage law with ordinary
multiplication. It retains the original law in its statement. Vanishing of
the correction, hence equality in the original coordinate, remains separate.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentPairNaturality LaurentSquareZeroCoordinate
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
variable (B : Type) [CommRing B] [Algebra (Ring K 1) B]
local notation "q" => completeIdentityFirstCorrection K n h i
local notation "e" => algebraMap (Ring K 1) B (parameter K 1)
local notation "f" => RingHom.comp (algebraMap (Ring K 1) B) (algebraMap K (Ring K 1))
local notation "M" => completeIdentityFinitePointMul K n h i 1 B

/-- The actual first-order multiplication error is the explicit canonical coboundary. -/
theorem completeIdentityFinitePointMul_first_coboundary (u v : Bˣ) :
    (M u v).val = u.val * v.val +
      (e) * (u.val * eval₂ (f) v (q) + v.val * eval₂ (f) u (q) -
        eval₂ (f) (u * v) (q)) := by
  rw [completeIdentityFinitePointMul_one_val]
  congr 2
  have he := congrArg
    (fun F : K[T;T⁻¹][T;T⁻¹] →+* B ↦ F (completeIdentityFiniteMulObstruction K n h i 0))
    (pairEval₂_coeffMap (algebraMap K (Ring K 1)) (algebraMap (Ring K 1) B) u v)
  change LaurentPairEvaluation.pairEval u v (completeIdentityFirstObstructionLift K n h i) =
    pairEval₂ (f) u v (completeIdentityFiniteMulObstruction K n h i 0) at he
  exact he.trans (completeIdentityFirstCorrection_formula K n h i (f) u v)

/-- The canonical correction gives a bijection with an explicit inverse. -/
def completeIdentityFirstCoordinateEquiv : Bˣ ≃ Bˣ :=
  changeEquiv (f) (e) (completeIdentityFirstWeight_sq K B) (q)

/-- Its coordinate is the original coordinate plus the canonical correction. -/
theorem completeIdentityFirstCoordinateEquiv_val (u : Bˣ) :
    (completeIdentityFirstCoordinateEquiv K n h i B u).val =
      u.val + (e) * eval₂ (f) u (q) := rfl

/-- The bijection intertwines the original first-order law with unit products. -/
theorem completeIdentityFirstCoordinateEquiv_mul (u v : Bˣ) :
    completeIdentityFirstCoordinateEquiv K n h i B (M u v) =
      completeIdentityFirstCoordinateEquiv K n h i B u *
        completeIdentityFirstCoordinateEquiv K n h i B v :=
  change_mul_of_coboundary (f) (e) (completeIdentityFirstWeight_sq K B) (q) (M)
    (completeIdentityFinitePointMul_first_coboundary K n h i B) u v

/-- The correction bijection fixes the original identity on every coefficient algebra. -/
theorem completeIdentityFirstCoordinateEquiv_one :
    completeIdentityFirstCoordinateEquiv K n h i B 1 = 1 := by
  apply change_one (f) (e) (completeIdentityFirstWeight_sq K B) (q)
  have he := congrArg (fun F : K[T;T⁻¹] →+* B ↦ F (q))
    (eval₂_map (RingHom.id K) (f) (1 : Kˣ))
  simp only [RingHom.comp_apply, RingHom.comp_id, map_one,
    completeIdentityFirstCorrection_at_one, map_zero] at he
  exact he.symm

end FLT.Mazur.PolygonInfinitesimalStages
