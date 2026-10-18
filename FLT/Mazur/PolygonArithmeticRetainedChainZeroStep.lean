/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainZero
public import FLT.Mazur.PolygonArithmeticRetainedChainStep
public import FLT.Mazur.PolygonArithmeticSimultaneousStep

/-!
# The full-chain step recovers the constructed depth-zero step

At depth zero the same retained node supplies both boundary corrections. There
is no internal edge, and the initial and common terminal drifts agree exactly.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages
variable {R : Type*} [CommRing R] {π : R}
  (S : PolygonArithmeticSimultaneous.State R π) (r : ℕ)
  (q : Bool → Bool → R[T;T⁻¹])

/-- Transfer the two existing depth-zero fields to their actual boundary edges. -/
def depthZeroFields : Edge 0 → Bool → R[T;T⁻¹]
  | .initial => q false
  | .incoming i => Fin.elim0 i
  | .closing => q true

/-- Both fields at the one retained node recover the existing depth-zero fields. -/
theorem depthZeroFields_retained (i : Fin 1) (b a : Bool) :
    retainedField (depthZeroFields q) i b a = PolygonArithmeticSimultaneous.lastField q b a := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  cases a
  · rfl
  · change LaurentBoundaryVectorField.reciprocalField
      (LaurentBoundaryCorrectionSplit.nonpositivePart
        (depthZeroFields q (outgoingEdge (Fin.last 0)) b)) = _
    rw [outgoingEdge_last]
    rfl

/-- The entire full-chain step specializes to the existing step, including both edges. -/
theorem ofDepthZero_step :
    (ofDepthZero S).step r (depthZeroFields q) = ofDepthZero (S.step r q) := by
  have hv (i : Fin 1) (b : Bool) :
      retainedInput (π := π) r (depthZeroFields q) i b =
        PolygonArithmeticSimultaneous.lastInput (π := π) r q b := by
    funext a
    unfold retainedInput PolygonArithmeticSimultaneous.lastInput
    rw [depthZeroFields_retained]
  change State.mk _ _ _ _ = State.mk _ _ _ _
  congr 1
  · funext m i b
    rw [hv]
    rfl
  · funext e m b
    cases e with
    | initial =>
      change ((twoBranchCorrectionPunctureFactor R π m _ _ false).trans _).trans _ = _
      rw [hv]
      rfl
    | incoming i => exact Fin.elim0 i
    | closing =>
      change ((twoBranchCorrectionRebasedPunctureFactor R π m _ _ b).symm.trans _).trans _ = _
      unfold State.outgoingFactor
      rw [hv]
      rfl

end FLT.Mazur.PolygonArithmeticRetainedChain
