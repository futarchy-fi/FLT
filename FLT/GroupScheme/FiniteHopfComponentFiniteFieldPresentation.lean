/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteHopfComponentRegularPresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.FiniteFieldPresentationDescent

/-! # Finite-field equations for the actual geometric Hopf components -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace HopfAlgebra

open FiniteAlgebra MvPolynomial


variable {k Ω A : Type u} [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  [IsAlgClosed Ω] [CommRing A] [HopfAlgebra Ω A] [IsArtinianRing A] [Module.Finite Ω A]
  (p : ℕ) [Fact p.Prime] [CharP Ω p]

include p

/-- A geometric Hopf component's localized regular equations descend to a finite
field, and coefficient-field base change reconstructs the original component. -/
theorem exists_component_finite_field_presentation (m : ComponentIndex A) :
    ∃ (n : ℕ) (E : IntermediateField k Ω), FiniteDimensional k E ∧
      ∃ qs : List (OriginLocalization E n), qs.length = n ∧
        RingTheory.Sequence.IsRegular (OriginLocalization E n) qs ∧
        Nonempty ((Ω ⊗[E] (OriginLocalization E n ⧸ Ideal.ofList qs)) ≃ₐ[Ω] Component A m) := by
  obtain ⟨n, rs, hlen, hreg, ⟨e⟩⟩ := exists_component_regular_presentation (k := Ω) p m
  obtain ⟨E, hE, qs, _, hlen', hreg', e', _⟩ :=
    exists_finite_field_regular_presentation (k := k) rs hreg e
  exact ⟨n, E, hE, qs, hlen'.trans hlen, hreg', ⟨e'⟩⟩

end HopfAlgebra
