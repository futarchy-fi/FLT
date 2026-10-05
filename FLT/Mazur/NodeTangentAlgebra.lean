/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTangent
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree

/-!
# The algebra adjoining a nodal tangent

The monic tangent quadratic has a canonical conjugation, sending its root s
to -a₁-s. This construction works integrally, including in characteristic two.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve Polynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The monic tangent quadratic at a singularity normalized to the origin. -/
noncomputable def nodeTangentPolynomial : R[X] := X ^ 2 + C W.a₁ * X - C W.a₂

/-- The tangent quadratic is monic over any coefficient ring. -/
theorem nodeTangentPolynomial_monic : (nodeTangentPolynomial W).Monic := by
  unfold nodeTangentPolynomial
  monicity!

/-- The tangent quadratic has degree two. -/
theorem nodeTangentPolynomial_degree [Nontrivial R] :
    (nodeTangentPolynomial W).degree = 2 := by
  simpa [nodeTangentPolynomial, sub_eq_add_neg] using
    (degree_quadratic (a := (1 : R)) (b := W.a₁) (c := -W.a₂) one_ne_zero)

/-- Evaluation of the tangent quadratic after any coefficient map. -/
@[simp] theorem nodeTangentPolynomial_eval₂ {S : Type*} [CommRing S]
    (f : R →+* S) (s : S) :
    (nodeTangentPolynomial W).eval₂ f s = s ^ 2 + f W.a₁ * s - f W.a₂ := by
  simp [nodeTangentPolynomial]

/-- The adjoined tangent satisfies the integral tangent equation. -/
theorem nodeTangentRoot_equation :
    (AdjoinRoot.root (nodeTangentPolynomial W)) ^ 2 +
      algebraMap R _ W.a₁ * AdjoinRoot.root (nodeTangentPolynomial W) -
      algebraMap R _ W.a₂ = 0 := by
  simpa only [nodeTangentPolynomial_eval₂, ← AdjoinRoot.algebraMap_eq] using
    AdjoinRoot.eval₂_root (nodeTangentPolynomial W)

/-- The other root is -a₁-s, without dividing by two. -/
theorem nodeTangentRoot_conjugate_equation :
    (nodeTangentPolynomial W).eval₂ (algebraMap R _)
      (-algebraMap R _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W)) = 0 := by
  rw [nodeTangentPolynomial_eval₂]
  linear_combination nodeTangentRoot_equation W

/-- The algebra endomorphism exchanging the two tangent roots. -/
noncomputable def nodeTangentConjugationHom :
    AdjoinRoot (nodeTangentPolynomial W) →ₐ[R] AdjoinRoot (nodeTangentPolynomial W) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _)
    (-algebraMap R _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W))
    (nodeTangentRoot_conjugate_equation W)

/-- Conjugation sends the distinguished root to its companion. -/
@[simp] theorem nodeTangentConjugationHom_root :
    nodeTangentConjugationHom W (AdjoinRoot.root (nodeTangentPolynomial W)) =
      -algebraMap R _ W.a₁ - AdjoinRoot.root (nodeTangentPolynomial W) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Exchanging the tangent roots twice is the identity on the entire algebra. -/
theorem nodeTangentConjugationHom_involutive :
    Function.Involutive (nodeTangentConjugationHom W) := by
  have h : (nodeTangentConjugationHom W).comp (nodeTangentConjugationHom W) =
      AlgHom.id R (AdjoinRoot (nodeTangentPolynomial W)) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, nodeTangentConjugationHom_root, map_sub, map_neg,
      AlgHom.commutes, AlgHom.id_apply]
    ring
  intro x
  exact DFunLike.congr_fun h x

/-- The canonical integral involution of the tangent splitting algebra. -/
noncomputable def nodeTangentConjugation :
    AdjoinRoot (nodeTangentPolynomial W) ≃ₐ[R] AdjoinRoot (nodeTangentPolynomial W) :=
  AlgEquiv.ofAlgHom (nodeTangentConjugationHom W) (nodeTangentConjugationHom W)
    (AlgHom.ext (nodeTangentConjugationHom_involutive W))
    (AlgHom.ext (nodeTangentConjugationHom_involutive W))

end FLT.Mazur
