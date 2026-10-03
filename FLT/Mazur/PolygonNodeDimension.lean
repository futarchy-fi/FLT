/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralDimension
public import FLT.Mazur.PolygonNormalizationAlgebra
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.KrullDimension.Field
/-!
# Dimensions of the polygon node rings

The finite normalization rings bound the node dimensions above by going up
and below by incomparability. The split normalization has a polynomial
quotient, and both normalization rings have dimension at most one.
-/

@[expose] public section
open Polynomial
namespace FLT.Mazur.PolygonNodeDimension
open PolygonNodeEqualizer PolygonNodePresentation PolygonNormalizationAlgebra
variable (K : Type*) [Field K]
/-- A polynomial ring over a field has dimension one. -/
theorem polynomial : ringKrullDim K[X] = 1 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
/-- The split affine node has dimension one. -/
theorem node : ringKrullDim (A (R := K)) = 1 := by
  apply le_antisymm
  · exact (IntegralDimension.le (A (R := K)) (K[X] × K[X]) node_comap_surjective).trans
      ((Ring.krullDimLE_iff (n := 1)).mp inferInstance)
  · have h := Algebra.QuasiFinite.ringKrullDim_le (A (R := K)) (K[X] × K[X])
    have h' := ringKrullDim_le_of_surjective (RingHom.fst K[X] K[X]) Prod.fst_surjective
    rw [polynomial K] at h'
    exact h'.trans h
/-- The irreducible one-gon node chart has dimension one. -/
theorem oneGon : ringKrullDim (B (R := K)) = 1 := by
  apply le_antisymm
  · exact (IntegralDimension.le (B (R := K)) K[X] oneGon_comap_surjective).trans
      (polynomial K).le
  · have h := Algebra.QuasiFinite.ringKrullDim_le (B (R := K)) K[X]
    rwa [polynomial K] at h
end FLT.Mazur.PolygonNodeDimension
