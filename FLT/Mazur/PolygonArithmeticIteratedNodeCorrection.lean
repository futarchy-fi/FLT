/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticTwoBranchCorrectionLift

/-!
# Iterated whole-node corrections with changing smoothings

A sequence of integral branch fields gives a recursive smoothing and a full
node equivalence back to the original node. Each step uses the smoothing
produced by the preceding step, without identifying it with a fixed parameter.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (t : Quotient R π m) (q : ℕ → Bool → R[T;T⁻¹])

/-- The exact smoothing after a finite sequence of full two-branch corrections. -/
def iteratedCorrectionSmoothing : ℕ → Quotient R π m
  | 0 => t
  | k + 1 => twoBranchCorrectionSmoothing R π m
      (iteratedCorrectionSmoothing k) (q k)

/-- The initial smoothing is the original parameter. -/
theorem iteratedCorrectionSmoothing_zero : iteratedCorrectionSmoothing R π m t q 0 = t := rfl

/-- The next correction starts at the previous exact smoothing. -/
theorem iteratedCorrectionSmoothing_succ (k : ℕ) :
    iteratedCorrectionSmoothing R π m t q (k + 1) =
      twoBranchCorrectionSmoothing R π m (iteratedCorrectionSmoothing R π m t q k) (q k) :=
  rfl

/-- Compose all whole-node equivalences, retaining their changing source rings. -/
def iteratedCorrectionNodeFactor : (k : ℕ) →
    ChartRing (iteratedCorrectionSmoothing R π m t q k) ≃ₐ[Quotient R π m] ChartRing t
  | 0 => AlgEquiv.refl
  | k + 1 => (twoBranchCorrectionNodeFactor R π m
      (iteratedCorrectionSmoothing R π m t q k) (q k)).trans
        (iteratedCorrectionNodeFactor k)

/-- The empty composite is the identity on the original full node. -/
theorem iteratedCorrectionNodeFactor_zero :
    iteratedCorrectionNodeFactor R π m t q 0 = AlgEquiv.refl := rfl

/-- The whole successor factor uses the actual intermediate node. -/
theorem iteratedCorrectionNodeFactor_succ (k : ℕ) :
    iteratedCorrectionNodeFactor R π m t q (k + 1) =
      (twoBranchCorrectionNodeFactor R π m
        (iteratedCorrectionSmoothing R π m t q k) (q k)).trans
          (iteratedCorrectionNodeFactor R π m t q k) := rfl

end FLT.Mazur.PolygonArithmeticStages
