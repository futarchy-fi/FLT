/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodePresentation
/-!
# Pinching neighborhoods over an arbitrary ring

At every prime of the parameter ring, the endpoints admit saturated principal
neighborhoods. Their common value avoids that prime; no division is used.
-/

@[expose] public noncomputable section
open Polynomial TopologicalSpace
namespace FLT.Mazur.RelativePinchingNeighborhoods
open PolygonNodeEqualizer PolygonNodePresentation
variable {R : Type*} [CommRing R]
/-- The endpoint over a specified prime of the base ring. -/
def point (a : R) (x : PrimeSpectrum R) : PrimeSpectrum R[X] :=
  PrimeSpectrum.comap (evalRingHom a) x
theorem mem_basicOpen_point (a : R) (x : PrimeSpectrum R) (p : R[X]) :
    point a x ∈ PrimeSpectrum.basicOpen p ↔ p.eval a ∉ x.asIdeal := Iff.rfl

/-- A principal neighborhood whose endpoint value avoids the base prime. -/
theorem principal_neighborhood (a : R) (x : PrimeSpectrum R)
    (U : Opens (PrimeSpectrum R[X])) (h : point a x ∈ U) :
    ∃ p : R[X], p.eval a ∉ x.asIdeal ∧ PrimeSpectrum.basicOpen p ≤ U := by
  obtain ⟨_, ⟨p, rfl⟩, hp, hU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h U.isOpen
  exact ⟨p, hp, hU⟩

/-- Saturated neighborhoods of the two node branches over any base prime. -/
theorem node_neighborhood (x : PrimeSpectrum R) (U V : Opens (PrimeSpectrum R[X]))
    (hU : point 0 x ∈ U) (hV : point 0 x ∈ V) :
    ∃ s : A (R := R), aEval s ∉ x.asIdeal ∧
      PrimeSpectrum.basicOpen (first s) ≤ U ∧ PrimeSpectrum.basicOpen (second s) ≤ V := by
  obtain ⟨p, hp, hpU⟩ := principal_neighborhood 0 x U hU
  obtain ⟨q, hq, hqV⟩ := principal_neighborhood 0 x V hV
  let s : A (R := R) := ⟨(C (q.eval 0) * p, C (p.eval 0) * q), by
    simp [mem_A, mul_comm]⟩
  refine ⟨s, ?_, (PrimeSpectrum.basicOpen_mul_le_right _ _).trans hpU,
    (PrimeSpectrum.basicOpen_mul_le_right _ _).trans hqV⟩
  change (C (q.eval 0) * p).eval 0 ∉ x.asIdeal
  simpa using x.isPrime.mul_notMem hq hp

/-- A saturated neighborhood of both one-gon endpoints over any base prime. -/
theorem oneGon_neighborhood (x : PrimeSpectrum R) (U : Opens (PrimeSpectrum R[X]))
    (h₀ : point 0 x ∈ U) (h₁ : point 1 x ∈ U) :
    ∃ s : B (R := R), bEval s ∉ x.asIdeal ∧ PrimeSpectrum.basicOpen s.val ≤ U := by
  obtain ⟨p, hp, hpU⟩ := principal_neighborhood 0 x U h₀
  obtain ⟨q, hq, hqU⟩ := principal_neighborhood 1 x U h₁
  let r := (1 - X) * (C (q.eval 1) * p) + X * (C (p.eval 0) * q)
  have hr₀ : r.eval 0 = p.eval 0 * q.eval 1 := by simp [r, mul_comm]
  have hr₁ : r.eval 1 = p.eval 0 * q.eval 1 := by simp [r]
  refine ⟨⟨r, (mem_B r).mpr (hr₀.trans hr₁.symm)⟩, ?_, ?_⟩
  · change r.eval 0 ∉ x.asIdeal
    rw [hr₀]
    exact x.isPrime.mul_notMem hp hq
  · intro y hy
    change r ∉ y.asIdeal at hy
    by_contra hn
    have hp' : p ∈ y.asIdeal := by
      by_contra h
      exact hn (hpU h)
    have hq' : q ∈ y.asIdeal := by
      by_contra h
      exact hn (hqU h)
    exact hy (y.asIdeal.add_mem
      (y.asIdeal.mul_mem_left _ (y.asIdeal.mul_mem_left _ hp'))
      (y.asIdeal.mul_mem_left _ (y.asIdeal.mul_mem_left _ hq')))
end FLT.Mazur.RelativePinchingNeighborhoods
