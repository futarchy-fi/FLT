/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentExtension
public import FLT.Mathlib.RingTheory.PowerBasisDifferentials
public import Mathlib.RingTheory.Unramified.Basic

/-!
# The tangent root algebra is unramified

A unit tangent discriminant makes the derivative invertible at the adjoined
root. Differentiating the tangent equation then kills the universal derivation
on that generator, hence on the whole algebra.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve Polynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The evaluated derivative of the monic tangent quadratic. -/
theorem nodeTangentPolynomial_aeval_derivative {S : Type*} [CommRing S] [Algebra R S]
    (s : S) : aeval s (nodeTangentPolynomial W).derivative = algebraMap R S W.a₁ + 2 * s := by
  simp [nodeTangentPolynomial, derivative_pow, derivative_mul]
  simp only [map_ofNat]
  ring

/-- The tangent root algebra is formally unramified whenever b₂ is a unit. -/
theorem nodeTangentAlgebra_formallyUnramified (hb : IsUnit W.b₂) :
    Algebra.FormallyUnramified R (AdjoinRoot (nodeTangentPolynomial W)) := by
  let S := AdjoinRoot (nodeTangentPolynomial W)
  let d := KaehlerDifferential.D R S
  let pb := (AdjoinRoot.isAdjoinRootMonic _ (nodeTangentPolynomial_monic W)).powerBasis
  have hz : d (AdjoinRoot.root (nodeTangentPolynomial W)) = 0 := by
    apply (nodeTangentRoot_derivative_isUnit W hb).smul_eq_zero.mp
    have h := d.comp_aeval_eq (AdjoinRoot.root (nodeTangentPolynomial W))
      (nodeTangentPolynomial W)
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero,
      nodeTangentPolynomial_aeval_derivative] at h
    exact h.symm
  have hd : d = 0 := pb.derivation_eq_zero d hz
  refine ⟨?_⟩
  suffices (⊤ : Submodule S (KaehlerDifferential R S)) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun x => this trivial
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  change d x = 0
  rw [hd]
  rfl

/-- The tangent conjugation is nontrivial when the transverse derivative is a unit. -/
theorem nodeTangentConjugation_ne_refl [Nontrivial R] (hb : IsUnit W.b₂) :
    nodeTangentConjugation W ≠ AlgEquiv.refl := by
  let : Nontrivial (AdjoinRoot (nodeTangentPolynomial W)) :=
    Module.nontrivial_of_finrank_pos (by rw [nodeTangentAlgebra_finrank]; decide)
  intro he
  have hr : nodeTangentConjugation W (AdjoinRoot.root (nodeTangentPolynomial W)) =
      -algebraMap R _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) :=
    nodeTangentConjugationHom_root W
  rw [he] at hr
  change AdjoinRoot.root (nodeTangentPolynomial W) =
    -algebraMap R _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) at hr
  have hz : algebraMap R _ W.a₁ + 2 * AdjoinRoot.root (nodeTangentPolynomial W) = 0 := by
    linear_combination hr
  exact (nodeTangentRoot_derivative_isUnit W hb).ne_zero hz

end FLT.Mazur
