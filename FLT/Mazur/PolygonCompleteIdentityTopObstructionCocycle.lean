/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopPointCocycle
public import FLT.Mazur.LaurentPairStageLift

/-!
# The exact reduced cocycle at every successive smoothing order

Faithful top-layer scalar extraction removes the square-zero weight from
original associativity. The resulting reduced equation holds over arbitrary
coefficient rings, including rings with nilpotents.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPairNaturality LaurentPairStageLift
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "O" => completeIdentityFiniteMulObstruction K n h i m

/-- An established original lower law forces the full next reduced cocycle on every algebra. -/
theorem completeIdentityFiniteMulObstruction_top_cocycle
    (hm : completeIdentityFiniteMulDefect K n h i m = 0)
    {S : Type} [CommRing S] (f : K →+* S) (u v w : Sˣ) :
    w.val * pairEval₂ f u v (O) + pairEval₂ f (u * v) w (O) =
      u.val * pairEval₂ f v w (O) + pairEval₂ f u (v * w) (O) := by
  let a := algebraMap S (Ring S (m + 1))
  let U : Sˣ → (Ring S (m + 1))ˣ := Units.map a.toMonoidHom
  let _ := (stageCoefficientMap f (m + 1)).toAlgebra
  have ha := completeIdentityTopObstructionLift_cocycle K n h i m hm
    (Ring S (m + 1)) (U u) (U v) (U w)
  change stageCoefficientMap f (m + 1) (parameter K (m + 1)) ^ (m + 1) *
      ((U w).val * pairEval₂ (stageCoefficientMap f (m + 1)) (U u) (U v)
        (completeIdentityTopObstructionLift K n h i m) +
        pairEval₂ (stageCoefficientMap f (m + 1)) (U u * U v) (U w)
          (completeIdentityTopObstructionLift K n h i m)) =
    stageCoefficientMap f (m + 1) (parameter K (m + 1)) ^ (m + 1) *
      ((U u).val * pairEval₂ (stageCoefficientMap f (m + 1)) (U v) (U w)
        (completeIdentityTopObstructionLift K n h i m) +
        pairEval₂ (stageCoefficientMap f (m + 1)) (U u) (U v * U w)
          (completeIdentityTopObstructionLift K n h i m)) at ha
  have hU (x y : Sˣ) : U x * U y = U (x * y) := (map_mul _ x y).symm
  have hval (x : Sˣ) : (U x).val = a x.val := rfl
  rw [stageCoefficientMap_parameter, hU, hU, hval, hval] at ha
  simp only [completeIdentityTopObstructionLift, U, a, pairEval₂_stageLift] at ha
  apply parameter_top_scalar_injective S (m + 1)
  simpa only [map_add, map_mul] using ha

end FLT.Mazur.PolygonInfinitesimalStages
