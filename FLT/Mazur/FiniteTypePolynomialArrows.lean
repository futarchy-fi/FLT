/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeRelationPresentation

/-!
# Polynomial representatives of arrows between finite-type algebras

Choose polynomial images of the source generators. The resulting polynomial
map recovers the entire original arrow and preserves the full relation ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w

variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  {B : Type w} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]

/-- Every original arrow has a polynomial representative on the chosen presentations. -/
theorem exists_polynomial_arrow (f : A →ₐ[R] B) :
    ∃ g : MvPolynomial (Fin (numGenerators R A)) R →ₐ[R]
      MvPolynomial (Fin (numGenerators R B)) R,
      (presentationMap R B).comp g = f.comp (presentationMap R A) := by
  choose x hx using fun i : Fin (numGenerators R A) ↦
    presentationMap_surjective R B (f (presentationMap R A (MvPolynomial.X i)))
  refine ⟨MvPolynomial.aeval x, ?_⟩
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hx i

/-- Polynomial recovery proves preservation of all original relations. -/
theorem polynomial_arrow_relations (f : A →ₐ[R] B)
    (g : MvPolynomial (Fin (numGenerators R A)) R →ₐ[R]
      MvPolynomial (Fin (numGenerators R B)) R)
    (hg : (presentationMap R B).comp g = f.comp (presentationMap R A)) :
    relationIdeal R A ≤ (relationIdeal R B).comap g.toRingHom := by
  intro z hz
  change presentationMap R B (g z) = 0
  change presentationMap R A z = 0 at hz
  have h := AlgHom.congr_fun hg z
  change presentationMap R B (g z) = f (presentationMap R A z) at h
  rw [h, hz, map_zero]

end FLT.Mazur.FiniteTypeRelationModel
