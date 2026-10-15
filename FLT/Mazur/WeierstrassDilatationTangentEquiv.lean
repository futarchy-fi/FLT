/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeAlgebra
public import FLT.Mazur.WeierstrassDilatationTangentEvaluation

/-!
# The full terminal quotient in polynomial tangent coordinates

The maps are inverse on all functions, with no puncture removed. The quotient
still retains the original product correction until its constant is extracted.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)
local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => DifferenceNode.Coordinate H b3
local notation "P" => DifferenceNode.p H b3
local notation "Q" => DifferenceNode.q H b3

/-- The complete tangent quotient evaluates on the original full terminal chart. -/
def terminalTangentBackward : B →ₐ[R] A :=
  DifferenceNode.evaluation H b3 (terminalSmallTangent W s b3 b4 b6 r)
    (terminalOppositeTangent W s b3 b4 b6 r)
    (terminalTangents_correction b3 b4 b6 r I hrI W s hI ha hr)

/-- The original divided cubic evaluates on the complete tangent quotient. -/
def terminalTangentForward : A →ₐ[R] B :=
  terminalTangentEvaluation W s b3 b4 b6 r I hI hrI ha hr P Q (DifferenceNode.relation H b3)

local notation "f" => terminalTangentForward W s b3 b4 b6 r I hI hrI ha hr
local notation "g" => terminalTangentBackward W s b3 b4 b6 r I hI hrI ha hr

/-- The backward comparison retains the small tangent label. -/
@[simp] theorem terminalTangentBackward_p : g P = terminalSmallTangent W s b3 b4 b6 r :=
  DifferenceNode.evaluation_p ..

/-- The backward comparison retains the opposite tangent label. -/
@[simp] theorem terminalTangentBackward_q : g Q = terminalOppositeTangent W s b3 b4 b6 r :=
  DifferenceNode.evaluation_q ..

/-- The forward comparison retains the full inverse horizontal coordinate. -/
@[simp] theorem terminalTangentForward_x :
    f (x W s b3 b4 b6) = (F).eval₂ (algebraMap R B) (Q - P - algebraMap R B b3) :=
  terminalTangentEvaluation_x ..

/-- The forward comparison retains the original vertical tangent shift. -/
@[simp] theorem terminalTangentForward_y :
    f (y W s b3 b4 b6) = P +
      (F).eval₂ (algebraMap R B) (Q - P - algebraMap R B b3) *
        r.eval₂ (algebraMap R B)
          ((F).eval₂ (algebraMap R B) (Q - P - algebraMap R B b3)) :=
  terminalTangentEvaluation_y ..

/-- The composite fixes every corrected tangent function. -/
theorem terminalTangentForward_backward : (f).comp g = AlgHom.id R B := by
  apply DifferenceNode.hom_ext
  · change f (g P) = P
    rw [terminalTangentBackward_p]
    exact terminalTangentEvaluation_small ..
  · change f (g Q) = Q
    rw [terminalTangentBackward_q]
    exact terminalTangentEvaluation_opposite ..

/-- The composite fixes every function of the original full terminal chart. -/
theorem terminalTangentBackward_forward : (g).comp f = AlgHom.id R A := by
  apply hom_ext
  · change g (f (x W s b3 b4 b6)) = x W s b3 b4 b6
    rw [terminalTangentForward_x, Polynomial.algHom_eval₂_algebraMap]
    simp only [map_sub, AlgHom.commutes, terminalTangentBackward_q, terminalTangentBackward_p]
    exact terminalInversePolynomial_original W r I hI hrI ha s b3 b4 b6
  · change g (f (y W s b3 b4 b6)) = y W s b3 b4 b6
    rw [terminalTangentForward_y]
    simp only [map_add, map_mul, Polynomial.algHom_eval₂_algebraMap, map_sub, AlgHom.commutes,
      terminalTangentBackward_p, terminalTangentBackward_q, terminalInversePolynomial_original]
    have he : r.eval₂ (algebraMap R A) (x W s b3 b4 b6) = algebraMap R[X] A r :=
      Polynomial.eval₂_algebraMap_X r (Algebra.algHom R R[X] A)
    rw [he, terminalSmallTangent, sub_add_cancel]

/-- The entire original terminal algebra is the constructed polynomial tangent quotient. -/
def terminalTangentEquiv : A ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom f g (terminalTangentForward_backward W s b3 b4 b6 r I hI hrI ha hr)
    (terminalTangentBackward_forward W s b3 b4 b6 r I hI hrI ha hr)

end FLT.Mazur.WeierstrassDilatation
