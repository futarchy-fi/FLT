/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree

/-!
# The infinity chart as a monic cubic over the Z-coordinate line

A monic presentation supplies a free module over the polynomial ring in Z.
This is the first regularity foundation for removing the five-coordinate torsion.
-/

@[expose] public noncomputable section

open Polynomial WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The normalized cubic, monic in X over the polynomial ring in Z. -/
def infinityMonicPolynomial : R[X][X] :=
  X ^ 3 + (C (C W.a₂ * X) * X ^ 2 +
    C (C W.a₄ * X ^ 2 - C W.a₁ * X) * X +
      C (C W.a₆ * X ^ 3 - C W.a₃ * X ^ 2 - X))

/-- The presentation is monic over every coefficient ring, including rings with nilpotents. -/
theorem infinityMonicPolynomial_monic : (infinityMonicPolynomial W).Monic := by
  apply monic_X_pow_add
  compute_degree!

/-- Evaluating both variables recovers precisely the Y-normalized cubic equation. -/
theorem infinityMonicPolynomial_eval {S : Type*} [CommRing S]
    (f : R[X] →+* S) (x : S) :
    (infinityMonicPolynomial W).eval₂ f x =
      x ^ 3 + f (C W.a₂) * f X * x ^ 2 +
        (f (C W.a₄) * f X ^ 2 - f (C W.a₁) * f X) * x +
        (f (C W.a₆) * f X ^ 3 - f (C W.a₃) * f X ^ 2 - f X) := by
  simp only [infinityMonicPolynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    map_sub, map_mul, map_pow]
  ring

/-- The free monic model before comparison with the existing chart quotient. -/
abbrev InfinityMonicModel := AdjoinRoot (infinityMonicPolynomial W)

/-- This model is free over the polynomial ring in the Z coordinate. -/
theorem infinityMonicModel_free : Module.Free R[X] (InfinityMonicModel W) :=
  (infinityMonicPolynomial_monic W).free_adjoinRoot

/-- The model's distinguished X and Z satisfy the original projective equation. -/
theorem infinityMonicModel_equation :
    (W.map (algebraMap R (InfinityMonicModel W))).toProjective.Equation
      ![AdjoinRoot.root (infinityMonicPolynomial W), 1,
        algebraMap R[X] (InfinityMonicModel W) X] := by
  have h := AdjoinRoot.eval₂_root (infinityMonicPolynomial W)
  change (infinityMonicPolynomial W).eval₂
    (algebraMap R[X] (InfinityMonicModel W))
    (AdjoinRoot.root (infinityMonicPolynomial W)) = 0 at h
  rw [infinityMonicPolynomial_eval] at h
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  have hc (a : R) : algebraMap R[X] (InfinityMonicModel W) (C a) =
      algebraMap R (InfinityMonicModel W) a :=
    (IsScalarTower.algebraMap_apply R R[X] (InfinityMonicModel W) a).symm
  simp only [hc] at h
  linear_combination -h

end FLT.Mazur.WeierstrassIntegralChart
