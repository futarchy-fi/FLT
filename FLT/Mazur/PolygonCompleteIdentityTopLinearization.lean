/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentSquareZeroLinearization
public import FLT.Mazur.PolygonCompleteIdentityTopCorrection

/-!
# Explicit coordinate bijections for successive original identity laws

An established preceding law constructs a canonical coordinate bijection
intertwining the next original multiplication with ordinary multiplication.
The original coordinate is retained in every statement; proving the
correction vanishes requires the remaining original-node extension argument.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentPairNaturality LaurentSquareZeroCoordinate
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
variable (B : Type) [CommRing B] [Algebra (Ring K (m + 1)) B]
local notation "q" => completeIdentityTopCorrection K n h i m
local notation "e" => algebraMap (Ring K (m + 1)) B (parameter K (m + 1)) ^ (m + 1)
local notation "f" => RingHom.comp (algebraMap (Ring K (m + 1)) B) (algebraMap K (Ring K (m + 1)))
local notation "M" => completeIdentityFinitePointMul K n h i (m + 1) B

/-- The actual next-order multiplication error is the explicit canonical coboundary. -/
theorem completeIdentityFinitePointMul_top_coboundary
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) (u v : Bˣ) :
    (M u v).val = u.val * v.val +
      (e) * (u.val * eval₂ (f) v (q) + v.val * eval₂ (f) u (q) -
        eval₂ (f) (u * v) (q)) := by
  rw [completeIdentityFinitePointMul_top_val K n h i m hm]
  congr 2
  have he := congrArg
    (fun F : K[T;T⁻¹][T;T⁻¹] →+* B ↦ F (completeIdentityFiniteMulObstruction K n h i m))
    (pairEval₂_coeffMap (algebraMap K (Ring K (m + 1))) (algebraMap (Ring K (m + 1)) B) u v)
  change LaurentPairEvaluation.pairEval u v (completeIdentityTopObstructionLift K n h i m) =
    pairEval₂ (f) u v (completeIdentityFiniteMulObstruction K n h i m) at he
  exact he.trans (completeIdentityTopCorrection_formula K n h i m hm (f) u v)

/-- The canonical correction gives a bijection with an explicit inverse. -/
def completeIdentityTopCoordinateEquiv : Bˣ ≃ Bˣ :=
  changeEquiv (f) (e) (parameter_top_weight_sq K m B) (q)

/-- Its coordinate is the original coordinate plus the canonical correction. -/
theorem completeIdentityTopCoordinateEquiv_val (u : Bˣ) :
    (completeIdentityTopCoordinateEquiv K n h i m B u).val =
      u.val + (e) * eval₂ (f) u (q) := rfl

/-- The bijection intertwines the original next-order law with unit products. -/
theorem completeIdentityTopCoordinateEquiv_mul
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) (u v : Bˣ) :
    completeIdentityTopCoordinateEquiv K n h i m B (M u v) =
      completeIdentityTopCoordinateEquiv K n h i m B u *
        completeIdentityTopCoordinateEquiv K n h i m B v :=
  change_mul_of_coboundary (f) (e) (parameter_top_weight_sq K m B) (q) (M)
    (completeIdentityFinitePointMul_top_coboundary K n h i m B hm) u v

/-- The correction bijection fixes the original identity on every coefficient algebra. -/
theorem completeIdentityTopCoordinateEquiv_one
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) :
    completeIdentityTopCoordinateEquiv K n h i m B 1 = 1 := by
  apply change_one (f) (e) (parameter_top_weight_sq K m B) (q)
  have he := congrArg (fun F : K[T;T⁻¹] →+* B ↦ F (q))
    (eval₂_map (RingHom.id K) (f) (1 : Kˣ))
  simp only [RingHom.comp_apply, RingHom.comp_id, map_one,
    completeIdentityTopCorrection_at_one K n h i m hm, map_zero] at he
  exact he.symm

end FLT.Mazur.PolygonInfinitesimalStages
