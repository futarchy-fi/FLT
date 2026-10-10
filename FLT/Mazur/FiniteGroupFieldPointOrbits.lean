/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantPolynomial
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Field-valued orbit separation for affine finite-group quotients

Two ring maps to a domain agree on the invariant ring precisely when one is
the other composed with a group element. A polynomial encodes one potential
separating coefficient for each element, forcing one common group element.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  {K : Type*} [CommRing K] [IsDomain K] (φ ψ : A →+* K)

/-- Equality on invariants detects the entire orbit of a domain-valued coordinate map. -/
theorem exists_ringHom_orbit (h : φ.comp (inclusion G A) = ψ.comp (inclusion G A)) :
    ∃ g : G, ψ = φ.comp (MulSemiringAction.toRingHom G A g) := by
  classical
  let _ := Fintype.ofFinite G
  by_contra hn
  have hne (g : G) : ψ ≠ φ.comp (MulSemiringAction.toRingHom G A g) :=
    fun hg ↦ hn ⟨g, hg⟩
  have hex (g : G) : ∃ a : A, ψ a ≠ φ (g • a) := by
    by_contra h
    push Not at h
    exact hne g (RingHom.ext h)
  choose a ha using hex
  let e := Fintype.equivFin G
  let P := Polynomial.ofFn (Fintype.card G) (fun i ↦ a (e.symm i))
  obtain ⟨g, hg⟩ := exists_polynomial_orbit G A φ ψ h P
  have hc := congrArg (fun Q : K[X] ↦ Q.coeff (e g).val) hg
  have hcoeff : P.coeff (e g).val = a g := by
    rw [ofFn_coeff_eq_val_of_lt _ (e g).isLt]
    exact congrArg a (e.symm_apply_apply g)
  rw [coeff_map, coeff_map, coeff_smul, hcoeff] at hc
  exact ha g hc

/-- Orbit equivalence is exactly equality of restrictions to the actual invariant ring. -/
theorem ringHom_invariants_eq_iff :
    φ.comp (inclusion G A) = ψ.comp (inclusion G A) ↔
      ∃ g : G, ψ = φ.comp (MulSemiringAction.toRingHom G A g) := by
  refine ⟨exists_ringHom_orbit G A φ ψ, ?_⟩
  rintro ⟨g, rfl⟩
  ext a
  change φ (inclusion G A a) = φ (g • inclusion G A a)
  rw [smul_inclusion]

end FLT.Mazur.FiniteGroupQuotient
