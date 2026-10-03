/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodePresentation

/-!
# Saturated principal neighborhoods of the pinching points

Open neighborhoods of the endpoints contain a principal neighborhood defined
by an element of the actual pinching ring, with value one at the node. These
are the neighborhoods needed to reduce arbitrary targets to affine charts.
-/

@[expose] public noncomputable section

open Polynomial TopologicalSpace

universe u

namespace FLT.Mazur.PinchingNeighborhoods

open PolygonNodeEqualizer PolygonNodePresentation

variable (K : Type u) [Field K]

/-- The point of the affine line with specified K-coordinate. -/
def point (a : K) : PrimeSpectrum K[X] := PrimeSpectrum.comap (evalRingHom a) ⊥

theorem mem_basicOpen_point (a : K) (p : K[X]) :
    point K a ∈ PrimeSpectrum.basicOpen p ↔ p.eval a ≠ 0 := by
  change ¬p.eval a ∈ (⊥ : Ideal K) ↔ _
  simp

/-- Choose a principal neighborhood inside any neighborhood of a rational point. -/
theorem principal_neighborhood (a : K) (U : Opens (PrimeSpectrum K[X]))
    (h : point K a ∈ U) :
    ∃ p : K[X], p.eval a ≠ 0 ∧ PrimeSpectrum.basicOpen p ≤ U := by
  obtain ⟨_, ⟨p, rfl⟩, hp, hU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h U.isOpen
  exact ⟨p, (mem_basicOpen_point K a p).mp hp, hU⟩

/-- Scale a polynomial to value one at a chosen point where it does not vanish. -/
def normalizedAt (a : K) (p : K[X]) : K[X] := C (p.eval a)⁻¹ * p

@[simp]
theorem normalizedAt_eval (a : K) (p : K[X]) (h : p.eval a ≠ 0) :
    (normalizedAt K a p).eval a = 1 := by simp [normalizedAt, h]

/-- Scaling does not enlarge the principal open. -/
theorem basicOpen_normalizedAt_le (a : K) (p : K[X]) :
    PrimeSpectrum.basicOpen (normalizedAt K a p) ≤ PrimeSpectrum.basicOpen p :=
  PrimeSpectrum.basicOpen_mul_le_right _ _

/-- Two origin neighborhoods admit a common element of the node ring with value one. -/
theorem node_neighborhood (U V : Opens (PrimeSpectrum K[X]))
    (hU : point K 0 ∈ U) (hV : point K 0 ∈ V) :
    ∃ s : A (R := K), aEval s = 1 ∧
      PrimeSpectrum.basicOpen (first s) ≤ U ∧ PrimeSpectrum.basicOpen (second s) ≤ V := by
  obtain ⟨p, hp, hpU⟩ := principal_neighborhood K 0 U hU
  obtain ⟨q, hq, hqV⟩ := principal_neighborhood K 0 V hV
  let s : A (R := K) := ⟨(normalizedAt K 0 p, normalizedAt K 0 q), by
    rw [mem_A]
    simp [hp, hq]⟩
  refine ⟨s, ?_, (basicOpen_normalizedAt_le K 0 p).trans hpU,
    (basicOpen_normalizedAt_le K 0 q).trans hqV⟩
  exact normalizedAt_eval K 0 p hp

/-- A neighborhood of both endpoints contains a principal neighborhood from B. -/
theorem oneGon_neighborhood (U : Opens (PrimeSpectrum K[X]))
    (h₀ : point K 0 ∈ U) (h₁ : point K 1 ∈ U) :
    ∃ s : B (R := K), bEval s = 1 ∧ PrimeSpectrum.basicOpen s.val ≤ U := by
  obtain ⟨p, hp, hpU⟩ := principal_neighborhood K 0 U h₀
  obtain ⟨q, hq, hqU⟩ := principal_neighborhood K 1 U h₁
  let r := (1 - X) * normalizedAt K 0 p + X * normalizedAt K 1 q
  have hr₀ : r.eval 0 = 1 := by simp [r, hp]
  have hr₁ : r.eval 1 = 1 := by simp [r, hq]
  refine ⟨⟨r, (mem_B r).mpr (hr₀.trans hr₁.symm)⟩, hr₀, ?_⟩
  intro x hx
  change r ∉ x.asIdeal at hx
  by_contra hn
  have hp' : p ∈ x.asIdeal := by
    by_contra h
    exact hn (hpU h)
  have hq' : q ∈ x.asIdeal := by
    by_contra h
    exact hn (hqU h)
  exact hx (x.asIdeal.add_mem
    (x.asIdeal.mul_mem_left _ (x.asIdeal.mul_mem_left _ hp'))
    (x.asIdeal.mul_mem_left _ (x.asIdeal.mul_mem_left _ hq')))

end FLT.Mazur.PinchingNeighborhoods
