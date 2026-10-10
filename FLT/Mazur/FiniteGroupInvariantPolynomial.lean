/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantRing

/-!
# Polynomial separation for finite-group quotients

Coordinate maps agreeing on invariants also agree on invariant polynomials.
The orbit polynomial then shows that, in a domain, one group element matches
all coefficients of any given polynomial at once.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A]
  {K : Type*} [CommRing K] (φ ψ : A →+* K)
  (h : φ.comp (inclusion G A) = ψ.comp (inclusion G A))

include h in
/-- Agreement on invariants extends coefficientwise to invariant polynomials. -/
theorem map_invariant_polynomial_eq (P : A[X]) (hP : ∀ g : G, g • P = P) :
    P.map φ = P.map ψ := by
  apply Polynomial.ext
  intro n
  rw [coeff_map, coeff_map]
  have hn : ∀ g : G, g • P.coeff n = P.coeff n := by
    intro g
    simpa only [coeff_smul] using congrArg (fun Q : A[X] ↦ Q.coeff n) (hP g)
  exact congrArg (fun f : invariantRing G A →+* K ↦ f ⟨P.coeff n, hn⟩) h

include h in
/-- The two coordinate maps give the same orbit polynomial with polynomial coefficients. -/
theorem map_polynomial_charpoly_eq [Fintype G] (P : A[X]) :
    (MulSemiringAction.charpoly G P).map (Polynomial.mapRingHom φ) =
      (MulSemiringAction.charpoly G P).map (Polynomial.mapRingHom ψ) := by
  apply Polynomial.ext
  intro n
  rw [coeff_map, coeff_map]
  exact map_invariant_polynomial_eq G A φ ψ h _
    (MulSemiringAction.smul_coeff_charpoly P n)

include h in
/-- In a domain a single group element matches all coefficients of the selected polynomial. -/
theorem exists_polynomial_orbit [Finite G] [IsDomain K] (P : A[X]) :
    ∃ g : G, P.map ψ = (g • P).map φ := by
  classical
  let _ := Fintype.ofFinite G
  have he : ((MulSemiringAction.charpoly G P).map (Polynomial.mapRingHom φ)).eval
      (P.map ψ) = 0 := by
    rw [map_polynomial_charpoly_eq G A φ ψ h]
    change ((MulSemiringAction.charpoly G P).map (Polynomial.mapRingHom ψ)).eval
      (Polynomial.mapRingHom ψ P) = 0
    rw [eval_map_apply, MulSemiringAction.eval_charpoly, map_zero]
  have hz : ∏ g : G, (P.map ψ - (g • P).map φ) = 0 := by
    simpa only [MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.coe_mapRingHom] using he
  obtain ⟨g, _, hg⟩ := Finset.prod_eq_zero_iff.mp hz
  exact ⟨g, sub_eq_zero.mp hg⟩

end FLT.Mazur.FiniteGroupQuotient
