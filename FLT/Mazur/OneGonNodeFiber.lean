/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonLocalizedPinching
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The fiber over the pinched point

The affine normalization has exactly two points over the node. A principal
neighborhood containing the node and the conductor puncture cover the chart.
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry
open FLT.Mazur.PolygonNodePresentation FLT.Mazur.OneGonPinchingAlgebra

namespace FLT.Mazur.OneGonNodeFiber

variable {K : Type*} [Field K]

/-- The point of the affine line given by evaluation at a scalar. -/
def endpoint (a : K) : PrimeSpectrum K[X] :=
  PrimeSpectrum.comap (evalRingHom a) ⟨⊥, inferInstance⟩

/-- The point of the pinched chart defined by its common endpoint value. -/
def nodePoint : PrimeSpectrum (B (R := K)) :=
  PrimeSpectrum.comap bEval.toRingHom ⟨⊥, inferInstance⟩

/-- A prime containing t-a is exactly the evaluation point a. -/
theorem eq_endpoint_of_mem (p : PrimeSpectrum K[X]) (a : K)
    (h : X - C a ∈ p.asIdeal) : p = endpoint a := by
  apply PrimeSpectrum.ext
  change p.asIdeal = RingHom.ker (evalRingHom a)
  symm
  apply (RingHom.ker_isMaximal_of_surjective (evalRingHom a)
    (fun r ↦ ⟨C r, by simp⟩)).eq_of_le p.isPrime.ne_top
  rw [ker_evalRingHom, Ideal.span_le, Set.singleton_subset_iff]
  exact h

/-- Only the two endpoints contain the conductor of the pinching. -/
theorem endpoints_of_conductor_mem (p : PrimeSpectrum K[X])
    (h : X * (X - 1) ∈ p.asIdeal) : p = endpoint 0 ∨ p = endpoint 1 := by
  rcases p.isPrime.mem_or_mem h with h0 | h1
  · exact Or.inl (eq_endpoint_of_mem p 0 (by simpa using h0))
  · exact Or.inr (eq_endpoint_of_mem p 1 (by simpa using h1))

@[simp]
theorem toPinching_endpoint_zero :
    toPinching (R := K) (endpoint 0) = nodePoint (K := K) := by
  apply PrimeSpectrum.ext
  rfl

@[simp]
theorem toPinching_endpoint_one :
    toPinching (R := K) (endpoint 1) = nodePoint (K := K) := by
  apply PrimeSpectrum.ext
  ext b
  change b.val.eval 1 = 0 ↔ b.val.eval 0 = 0
  rw [(mem_B _).mp b.property]

/-- The fiber over the node consists precisely of zero and one. -/
theorem fiber_node (p : PrimeSpectrum K[X]) :
    toPinching (R := K) p = nodePoint (K := K) ↔ p = endpoint 0 ∨ p = endpoint 1 := by
  constructor
  · intro hp
    have hu : u (R := K) ∈ (toPinching p).asIdeal := by
      rw [hp]
      change bEval u = 0
      simp [bEval, u]
    exact endpoints_of_conductor_mem p hu
  · rintro (rfl | rfl)
    · exact toPinching_endpoint_zero (K := K)
    · exact toPinching_endpoint_one (K := K)

/-- Any principal neighborhood of the node covers the chart with the conductor puncture. -/
theorem principal_puncture_cover (s : B (R := K)) (hs : bEval s ≠ 0)
    (y : PrimeSpectrum (B (R := K))) :
    y ∈ PrimeSpectrum.basicOpen s ∨ y ∈ PrimeSpectrum.basicOpen u := by
  by_cases hy : y ∈ PrimeSpectrum.basicOpen u
  · exact Or.inr hy
  · left
    have hu : u (R := K) ∈ y.asIdeal := by simpa using hy
    obtain ⟨p, rfl⟩ := toPinching_surjective y
    rcases endpoints_of_conductor_mem p hu with rfl | rfl
    · change bEval s ≠ 0
      exact hs
    · change s.val.eval 1 ≠ 0
      rw [← (mem_B _).mp s.property]
      exact hs

end FLT.Mazur.OneGonNodeFiber
