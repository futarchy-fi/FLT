/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Actual smooth points on the two punctured divided branches

At split nodal residue coefficients the two tangent lines supply actual
algebra maps from the same divided chart. Their vertical derivatives are
nonzero away from the crossing, so both maps land in the relative smooth
locus over the original ring, although their contractions are the node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (hs : algebraMap R K s = 0) (h2 : algebraMap R K W.a₂ = 0)
  (h3 : algebraMap R K b3 = 0) (h4 : algebraMap R K b4 = 0)
  (h6 : algebraMap R K b6 = 0)

/-- Either tangent branch gives an actual point of the original divided coordinate algebra. -/
def splitBranchEvaluation (b : Bool) (u : K) : Coordinate W s b3 b4 b6 →ₐ[R] K :=
  evaluation W s b3 b4 b6 u (if b then -algebraMap R K W.a₁ * u else 0) (by
    simp only [hs, h2, h3, h4, h6, zero_mul, add_zero]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring)

/-- The divided abscissa remains the chosen branch parameter. -/
@[simp] theorem splitBranchEvaluation_x (b : Bool) (u : K) :
    splitBranchEvaluation W s b3 b4 b6 hs h2 h3 h4 h6 b u (x W s b3 b4 b6) = u :=
  evaluation_x ..

/-- The divided ordinate is the corresponding tangent-line equation. -/
@[simp] theorem splitBranchEvaluation_y (b : Bool) (u : K) :
    splitBranchEvaluation W s b3 b4 b6 hs h2 h3 h4 h6 b u (y W s b3 b4 b6) =
      if b then -algebraMap R K W.a₁ * u else 0 :=
  evaluation_y ..

/-- The derivative is the signed tangent coefficient times the punctured parameter. -/
theorem splitBranchEvaluation_derivative (b : Bool) (u : K) :
    splitBranchEvaluation W s b3 b4 b6 hs h2 h3 h4 h6 b u
        (verticalDerivative W s b3 b4 b6) =
      if b then -(algebraMap R K W.a₁ * u) else algebraMap R K W.a₁ * u := by
  rw [verticalDerivative_eq]
  simp only [map_add, map_mul, map_ofNat, AlgHom.commutes,
    splitBranchEvaluation_x, splitBranchEvaluation_y, h3, add_zero]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

/-- Both punctured branches lie in the actual relative smooth locus of the divided chart. -/
theorem splitBranchEvaluation_range_smooth (b : Bool) (u : K)
    (ht : algebraMap R K W.a₁ ≠ 0) (hu : u ≠ 0) :
    Set.range (Spec.map (CommRingCat.ofHom
      (splitBranchEvaluation W s b3 b4 b6 hs h2 h3 h4 h6 b u).toRingHom)) ⊆
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W s b3 b4 b6)))).smoothLocus := by
  apply dividedFieldPoint_range_smooth
  rw [splitBranchEvaluation_derivative]
  cases b
  · exact mul_ne_zero ht hu
  · exact neg_ne_zero.mpr (mul_ne_zero ht hu)

end FLT.Mazur.WeierstrassDilatation
