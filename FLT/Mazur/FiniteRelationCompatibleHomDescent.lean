/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationFiniteHomDescent

/-!
# Compatible finite cones at relation stages

Adding an overlap or a triple intersection to a finite affine diagram requires
lifting all incoming arrows and preserving their previously specified
relations. This theorem constructs the new compatible cone from equations in
the limiting algebra; compatibility at a finite stage is an output.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- A finite cone with finite-type relations descends to a common relation stage. -/
theorem exists_compatible_hom_lift {ι : Type w} [Finite ι] {κ : Type z} [Finite κ]
    (A : ι → Type v) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FinitePresentation R (A i)]
    (C : κ → Type w) [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
    [∀ k, Algebra.FiniteType R (C k)] (l r : κ → ι)
    (a : ∀ k, C k →ₐ[R] A (l k)) (b : ∀ k, C k →ₐ[R] A (r k))
    (f : ∀ i, A i →ₐ[R] P ⧸ I)
    (h : ∀ k, (f (l k)).comp (a k) = (f (r k)).comp (b k)) (s : Finset I) :
    ∃ t : Finset I, s ≤ t ∧ ∃ g : ∀ i, A i →ₐ[R] Stage I t,
      (∀ i, (toQuotient R I t).comp (g i) = f i) ∧
      (∀ k, (g (l k)).comp (a k) = (g (r k)).comp (b k)) := by
  obtain ⟨t, hst, g, hg⟩ := exists_hom_lift_finite I A s f
  have he (k) : (toQuotient R I t).comp ((g (l k)).comp (a k)) =
      (toQuotient R I t).comp ((g (r k)).comp (b k)) := by
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hg, hg, h]
  obtain ⟨q, htq, hq⟩ := exists_hom_relations I A C l r a b t g he
  refine ⟨q, hst.trans htq, fun i ↦ (transition R I htq).comp (g i), ?_, hq⟩
  intro i
  rw [← AlgHom.comp_assoc, toQuotient_comp, hg]

end FLT.Mazur.FiniteRelationModel
