/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePolynomialStableStages
public import FLT.Mazur.FiniteTypePolynomialArrows

/-!
# Shared finite stages for diagrams of finite-type algebras

Construct every finite-stage arrow from its original algebra map. A single
relation set at each vertex serves all incoming and outgoing arrows, including
cycles. Every arrow recovers the specified original map on the full source.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {E : Type w} [Finite E]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)] (src dst : E → ι)

/-- All original arrows descend simultaneously with one shared stage per vertex. -/
theorem exists_finiteType_diagram_stages (f : ∀ e, A (src e) →ₐ[R] A (dst e))
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ t : ∀ i, Finset (relationIdeal R (A i)), s ≤ t ∧
      ∃ g : ∀ e, Stage R (A (src e)) (t (src e)) →ₐ[R]
        Stage R (A (dst e)) (t (dst e)),
        ∀ e, (stageMap R (A (dst e)) (t (dst e))).comp (g e) =
          (f e).comp (stageMap R (A (src e)) (t (src e))) := by
  choose p hp using fun e ↦ exists_polynomial_arrow (f e)
  have hI (e) := polynomial_arrow_relations (f e) (p e) (hp e)
  obtain ⟨t, ht, hrel⟩ := FinitePolynomialCoefficients.exists_stable_stages
    (fun i ↦ numGenerators R (A i)) src dst p (fun i ↦ relationIdeal R (A i)) hI s
  let g (e) : Stage R (A (src e)) (t (src e)) →ₐ[R]
      Stage R (A (dst e)) (t (dst e)) :=
    Ideal.quotientMapₐ (FiniteRelationModel.relations (relationIdeal R (A (dst e)))
      (t (dst e))) (p e) (hrel e)
  refine ⟨t, ht, g, fun e ↦ ?_⟩
  apply (AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective R
    (FiniteRelationModel.relations (relationIdeal R (A (src e))) (t (src e))))).mp
  apply AlgHom.ext
  intro z
  change presentationMap R (A (dst e)) (p e z) =
    f e (presentationMap R (A (src e)) z)
  exact AlgHom.congr_fun (hp e) z

end FLT.Mazur.FiniteTypeRelationModel
