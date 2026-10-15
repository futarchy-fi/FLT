/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentPairStageLift
public import FLT.Mazur.PolygonCompleteIdentityPointCocycle

/-!
# The actual reduced first obstruction is a multiplicative cocycle

Evaluate original associativity over the first smoothing stage of an arbitrary
coefficient algebra, then recover its top coefficient. This gives the exact
reduced cocycle equation, without a cardinality or reducedness assumption on
the coefficient algebra and without assuming the desired vanishing.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPairNaturality LaurentPairStageLift
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "O" => completeIdentityFiniteMulObstruction K n h i 0

/-- The canonical reduced first error satisfies the exact cocycle equation on every algebra. -/
theorem completeIdentityFiniteMulObstruction_zero_cocycle
    {S : Type} [CommRing S] (f : K →+* S) (u v w : Sˣ) :
    w.val * pairEval₂ f u v (O) + pairEval₂ f (u * v) w (O) =
      u.val * pairEval₂ f v w (O) + pairEval₂ f u (v * w) (O) := by
  let a := algebraMap S (Ring S 1)
  let U : Sˣ → (Ring S 1)ˣ := Units.map a.toMonoidHom
  let _ := (stageCoefficientMap f 1).toAlgebra
  have ha := completeIdentityFirstObstructionLift_cocycle K n h i (Ring S 1)
    (U u) (U v) (U w)
  change stageCoefficientMap f 1 (parameter K 1) *
      ((U w).val * pairEval₂ (stageCoefficientMap f 1) (U u) (U v)
        (completeIdentityFirstObstructionLift K n h i) +
        pairEval₂ (stageCoefficientMap f 1) (U u * U v) (U w)
          (completeIdentityFirstObstructionLift K n h i)) =
    stageCoefficientMap f 1 (parameter K 1) *
      ((U u).val * pairEval₂ (stageCoefficientMap f 1) (U v) (U w)
        (completeIdentityFirstObstructionLift K n h i) +
        pairEval₂ (stageCoefficientMap f 1) (U u) (U v * U w)
          (completeIdentityFirstObstructionLift K n h i)) at ha
  have hU (x y : Sˣ) : U x * U y = U (x * y) := (map_mul _ x y).symm
  have hval (x : Sˣ) : (U x).val = a x.val := rfl
  rw [stageCoefficientMap_parameter, hU, hU, hval, hval] at ha
  simp only [completeIdentityFirstObstructionLift, U, a, pairEval₂_stageLift] at ha
  apply parameter_scalar_one_injective (S := S)
  simpa only [map_add, map_mul] using ha

end FLT.Mazur.PolygonInfinitesimalStages
