/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorCoefficientDetection
public import FLT.Mazur.AffineRationalNonvanishing
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Density of original rational points after arbitrary coefficient extension

For a reduced finite-type affine algebra over an algebraically closed field,
original rational points remain dense after any field extension. In particular,
a nonempty open defined with transcendental coefficients contains an original
rational point; the open itself need not descend.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TensorCoefficientDetection
open scoped TensorProduct
variable {k K A : Type*} [Field k] [Field K] [Algebra k K]
  [CommRing A] [Algebra k A]

/-- The extended spectrum point defined by an original rational point. -/
def extendedPoint (p : A →ₐ[k] k) : PrimeSpectrum (K ⊗[k] A) :=
  ⟨RingHom.ker (evaluation (K := K) p), RingHom.ker_isPrime _⟩

/-- Basic open membership tests the actual extended function. -/
theorem extendedPoint_mem_basicOpen (p : A →ₐ[k] k) (x : K ⊗[k] A) :
    extendedPoint (K := K) p ∈ PrimeSpectrum.basicOpen x ↔ evaluation p x ≠ 0 := Iff.rfl

variable [IsAlgClosed k] [Algebra.FiniteType k A] [IsReduced A]

/-- Every nonzero extended function is detected by an original rational point. -/
theorem exists_evaluation_ne_zero (x : K ⊗[k] A) (hx : x ≠ 0) :
    ∃ p : A →ₐ[k] k, evaluation (K := K) p x ≠ 0 := by
  obtain ⟨a, ha, hd⟩ := exists_nonzero_detecting_coefficient x hx
  obtain ⟨p, hp⟩ := AffineRationalNonvanishing.exists_point_of_ne_zero (k := k) a ha
  exact ⟨p, hd p hp⟩

/-- Original rational points are dense even in the spectrum with extended coefficients. -/
theorem dense_extendedPoints :
    Dense (Set.range (extendedPoint (k := k) (K := K) (A := A))) := by
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff.mpr
  rintro _ ⟨x, rfl⟩ hn
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot,
      Set.not_nonempty_empty] at hn
  obtain ⟨p, hp⟩ := exists_evaluation_ne_zero x hx
  exact ⟨extendedPoint p, hp, ⟨p, rfl⟩⟩

/-- A nonempty open with arbitrary extended coefficients contains an original rational point. -/
theorem exists_extendedPoint_mem_open
    (U : TopologicalSpace.Opens (PrimeSpectrum (K ⊗[k] A)))
    (hU : (U : Set (PrimeSpectrum (K ⊗[k] A))).Nonempty) :
    ∃ p : A →ₐ[k] k, extendedPoint (K := K) p ∈ U := by
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := dense_extendedPoints.exists_mem_open U.isOpen hU
  exact ⟨p, hp⟩

end FLT.Mazur.TensorCoefficientDetection
