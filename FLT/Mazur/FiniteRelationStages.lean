/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.FinitePresentation

/-!
# Finite-relation approximations of an arbitrary quotient

A finite subset of an ideal gives a finitely generated relation ideal.
The quotient stages are finitely presented whenever the ambient algebra is.
No finite generation hypothesis is imposed on the full relation ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationModel

universe u v

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- Relations imposed at a finite stage. -/
def relations (s : Finset I) : Ideal P :=
  Ideal.span (Subtype.val '' (s : Set I))

/-- Every finite relation belongs to the full ideal. -/
theorem relations_le (s : Finset I) : relations I s ≤ I := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- Enlarging the finite set enlarges its relation ideal. -/
theorem relations_mono {s t : Finset I} (h : s ≤ t) : relations I s ≤ relations I t :=
  Ideal.span_mono (Set.image_mono h)

/-- A finite stage has a finitely generated relation ideal. -/
theorem relations_fg (s : Finset I) : (relations I s).FG :=
  Submodule.fg_span (s.finite_toSet.image Subtype.val)

/-- The quotient with only the specified finite relations. -/
abbrev Stage (s : Finset I) := P ⧸ relations I s

/-- Finite-relation stages of a finitely presented algebra are finitely presented. -/
instance stage_finitePresentation [Algebra.FinitePresentation R P] (s : Finset I) :
    Algebra.FinitePresentation R (Stage I s) :=
  Algebra.FinitePresentation.quotient (relations_fg I s)

variable (R)

/-- Transition to a larger finite relation set. -/
def transition {s t : Finset I} (h : s ≤ t) : Stage I s →ₐ[R] Stage I t :=
  Ideal.Quotient.factorₐ R (relations_mono I h)

/-- The canonical map to the full quotient. -/
def toQuotient (s : Finset I) : Stage I s →ₐ[R] P ⧸ I :=
  Ideal.Quotient.factorₐ R (relations_le I s)

/-- Transitions preserve polynomial representatives. -/
@[simp] theorem transition_mk {s t : Finset I} (h : s ≤ t) (x : P) :
    transition R I h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

/-- The comparison with the full quotient preserves representatives. -/
@[simp] theorem toQuotient_mk (s : Finset I) (x : P) :
    toQuotient R I s (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk I x := rfl

/-- Every transition is surjective. -/
theorem transition_surjective {s t : Finset I} (h : s ≤ t) :
    Function.Surjective (transition R I h) :=
  Ideal.Quotient.factor_surjective (relations_mono I h)

/-- Every quotient element is represented at every finite stage. -/
theorem toQuotient_surjective (s : Finset I) : Function.Surjective (toQuotient R I s) :=
  Ideal.Quotient.factor_surjective (relations_le I s)

/-- Transition maps respect composition. -/
theorem transition_comp {s t q : Finset I} (h : s ≤ t) (k : t ≤ q) :
    (transition R I k).comp (transition R I h) = transition R I (h.trans k) :=
  Ideal.Quotient.factorₐ_comp R _ _

/-- The maps to the full quotient form a compatible family. -/
theorem toQuotient_comp {s t : Finset I} (h : s ≤ t) :
    (toQuotient R I t).comp (transition R I h) = toQuotient R I s :=
  Ideal.Quotient.factorₐ_comp R _ _

end FLT.Mazur.FiniteRelationModel
