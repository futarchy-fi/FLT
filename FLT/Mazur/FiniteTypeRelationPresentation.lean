/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationStages

/-!
# Polynomial presentations of finite-type algebras

Choose finitely many generators, retaining the full, possibly infinitely
generated kernel. Finite subsets of this kernel give finitely presented
algebras mapping surjectively to the original finite-type algebra.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable (R : Type u) [CommRing R] (B : Type v) [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B]

/-- Number of generators in a chosen finite-type presentation. -/
def numGenerators : ℕ :=
  (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)).choose

/-- The chosen polynomial presentation map. -/
def presentationMap : MvPolynomial (Fin (numGenerators R B)) R →ₐ[R] B :=
  (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)).choose_spec.choose

/-- The presentation map is surjective. -/
theorem presentationMap_surjective : Function.Surjective (presentationMap R B) :=
  (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)).choose_spec.choose_spec

/-- All relations among the chosen generators, without a finiteness assumption. -/
def relationIdeal : Ideal (MvPolynomial (Fin (numGenerators R B)) R) :=
  RingHom.ker (presentationMap R B).toRingHom

/-- The original algebra is the quotient by its full relation ideal. -/
def quotientEquiv :
    (MvPolynomial (Fin (numGenerators R B)) R ⧸ relationIdeal R B) ≃ₐ[R] B :=
  Ideal.quotientKerAlgEquivOfSurjective (presentationMap_surjective R B)

/-- An approximating algebra with finitely many of the original relations. -/
abbrev Stage (s : Finset (relationIdeal R B)) :=
  FiniteRelationModel.Stage (relationIdeal R B) s

/-- Every approximating algebra is finitely presented over the original base. -/
instance stage_finitePresentation (s : Finset (relationIdeal R B)) :
    Algebra.FinitePresentation R (Stage R B s) := inferInstance

/-- Each approximating algebra maps to the original algebra. -/
def stageMap (s : Finset (relationIdeal R B)) : Stage R B s →ₐ[R] B :=
  (quotientEquiv R B).toAlgHom.comp (FiniteRelationModel.toQuotient R (relationIdeal R B) s)

/-- Stage maps evaluate the original polynomial representatives. -/
@[simp] theorem stageMap_mk (s : Finset (relationIdeal R B))
    (x : MvPolynomial (Fin (numGenerators R B)) R) :
    stageMap R B s (Ideal.Quotient.mk _ x) = presentationMap R B x := rfl

/-- Every stage maps surjectively onto the original finite-type algebra. -/
theorem stageMap_surjective (s : Finset (relationIdeal R B)) :
    Function.Surjective (stageMap R B s) :=
  (quotientEquiv R B).surjective.comp
    (FiniteRelationModel.toQuotient_surjective R (relationIdeal R B) s)

/-- Evaluation at the original algebra commutes with imposing more relations. -/
theorem stageMap_transition {s t : Finset (relationIdeal R B)} (h : s ≤ t) :
    (stageMap R B t).comp (FiniteRelationModel.transition R (relationIdeal R B) h) =
      stageMap R B s := by
  rw [stageMap, AlgHom.comp_assoc, FiniteRelationModel.toQuotient_comp]
  rfl

end FLT.Mazur.FiniteTypeRelationModel
