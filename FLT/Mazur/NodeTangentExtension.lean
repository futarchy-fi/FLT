/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentAlgebra
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.AdjoinRoot
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# An integral quadratic extension splitting a nonsplit tangent

Irreducibility of the residue tangent quadratic makes its integral root algebra
a DVR. The original uniformizer still generates its maximal ideal. The root
has unit transverse derivative whenever the tangent discriminant is a unit.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve Polynomial

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The square of the transverse derivative is the tangent discriminant. -/
theorem nodeTangentRoot_derivative_sq :
    (algebraMap R _ W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W)) ^ 2 =
      algebraMap R _ W.b₂ := by
  simp only [b₂, map_add, map_pow, map_mul, map_ofNat]
  linear_combination 4 * nodeTangentRoot_equation W

/-- A unit tangent discriminant gives a unit transverse derivative, even above two. -/
theorem nodeTangentRoot_derivative_isUnit (hb : IsUnit W.b₂) :
    IsUnit (algebraMap R _ W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W)) := by
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [nodeTangentRoot_derivative_sq]
  exact hb.map (algebraMap R _)

/-- The integral root algebra has rank two. -/
theorem nodeTangentAlgebra_finrank [Nontrivial R] :
    Module.finrank R (AdjoinRoot (nodeTangentPolynomial W)) = 2 := by
  exact (AdjoinRoot.isAdjoinRootMonic _ (nodeTangentPolynomial_monic W)).finrank.trans
    (natDegree_eq_of_degree_eq_some (nodeTangentPolynomial_degree W))

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- A nonsplit residue tangent lifts to a finite quadratic DVR extension with the same
uniformizer and a root of unit transverse derivative. -/
theorem exists_node_tangent_extension
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue R)))
    (hb : IsUnit W.b₂) (π : R) (hπ : maximalIdeal R = Ideal.span {π}) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra R S) (_ : Module.Finite R S) (_ : IsLocalHom (algebraMap R S)),
      Module.finrank R S = 2 ∧
      maximalIdeal S = Ideal.span {algebraMap R S π} ∧
      ∃ s : S, s ^ 2 + algebraMap R S W.a₁ * s - algebraMap R S W.a₂ = 0 ∧
        IsUnit (algebraMap R S W.a₁ + 2 * s) := by
  let P := nodeTangentPolynomial W
  have hm : P.Monic := nodeTangentPolynomial_monic W
  have hi : Irreducible P := hm.irreducible_of_irreducible_map (residue R) P hirr
  let : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi)
  have hd : P.degree ≠ 0 := by rw [nodeTangentPolynomial_degree]; norm_num
  obtain ⟨hmax, hDVR, hlocal⟩ :=
    AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hm hd hirr
  let := hDVR
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, hDVR, inferInstance,
    hm.finite_adjoinRoot, hlocal, nodeTangentAlgebra_finrank W, ?_,
    AdjoinRoot.root P, nodeTangentRoot_equation W, nodeTangentRoot_derivative_isUnit W hb⟩
  rw [← IsLocalRing.eq_maximalIdeal hmax, hπ, Ideal.map_span, Set.image_singleton]

end FLT.Mazur
