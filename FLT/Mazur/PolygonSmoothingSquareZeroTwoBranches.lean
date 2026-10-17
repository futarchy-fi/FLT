/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingSquareZeroEdgeFactors

/-!
# Independent square-zero corrections on both punctures of one node

Reflect the second correction across the actual branch interchange, then
compose on the whole node. Each puncture sees exactly its own positive field.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t e : R) (he : e ^ 2 = 0) (het : e * t = 0)
local notation "L" => R[T;T⁻¹]
local notation "l" => leftLaurentMap t
local notation "r" => AlgHom.comp (leftLaurentMap t) (branchSwapMap t)
local notation "s" => branchSwapMap t

/-- The positive correction transported to the second original branch. -/
irreducible_def squareZeroReflectedFactor (q : L) : ChartRing t ≃ₐ[R] ChartRing t :=
  (branchSwap t).trans ((squareZeroPositiveFactor t e he het q).trans (branchSwap t))

/-- Reflection makes the first puncture the unchanged opposite puncture. -/
theorem squareZeroReflectedFactor_left (q : L) :
    (l).comp (squareZeroReflectedFactor t e he het q).toAlgHom = l := by
  rw [squareZeroReflectedFactor_def]
  change (l).comp ((s).comp ((squareZeroPositiveFactor t e he het q).toAlgHom.comp s)) = l
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, squareZeroPositiveFactor_right,
    AlgHom.comp_assoc, branchSwapMap_comp, AlgHom.comp_id]

/-- The second puncture has exactly its prescribed positive field. -/
theorem squareZeroReflectedFactor_right (q : L) :
    (r).comp (squareZeroReflectedFactor t e he het q).toAlgHom =
      (LaurentSquareZeroAutomorphism.subst e he (positivePart q)).comp r := by
  rw [squareZeroReflectedFactor_def]
  change ((l).comp s).comp
    ((s).comp ((squareZeroPositiveFactor t e he het q).toAlgHom.comp s)) = _
  rw [AlgHom.comp_assoc l s, ← AlgHom.comp_assoc s s, branchSwapMap_comp,
    AlgHom.id_comp, ← AlgHom.comp_assoc, squareZeroPositiveFactor_left, AlgHom.comp_assoc]

/-- One full node automorphism realizes the two independently given boundary corrections. -/
irreducible_def squareZeroTwoBranchFactor (q : Bool → L) : ChartRing t ≃ₐ[R] ChartRing t :=
  (squareZeroPositiveFactor t e he het (q true)).trans
    (squareZeroReflectedFactor t e he het (q false))

/-- Both puncture squares use this same complete node automorphism. -/
theorem squareZeroTwoBranchFactor_boundary (q : Bool → L) (b : Bool) :
    (if b then l else r).comp (squareZeroTwoBranchFactor t e he het q).toAlgHom =
      (LaurentSquareZeroAutomorphism.subst e he (positivePart (q b))).comp
        (if b then l else r) := by
  rw [squareZeroTwoBranchFactor_def]
  cases b
  · change (r).comp ((squareZeroReflectedFactor t e he het (q false)).toAlgHom.comp
      (squareZeroPositiveFactor t e he het (q true)).toAlgHom) = _
    rw [← AlgHom.comp_assoc, squareZeroReflectedFactor_right,
      AlgHom.comp_assoc, squareZeroPositiveFactor_right]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · change (l).comp ((squareZeroReflectedFactor t e he het (q false)).toAlgHom.comp
      (squareZeroPositiveFactor t e he het (q true)).toAlgHom) = _
    rw [← AlgHom.comp_assoc, squareZeroReflectedFactor_left, squareZeroPositiveFactor_left]
    simp only [↓reduceIte]

end FLT.Mazur.PolygonSmoothing
