/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceExistence

/-!+# One ambient index for source charts and shared overlaps

The disjoint union keeps each overlap label exactly once. Source vertices
retain all their principal opens; overlap vertices have their one specified
principal open. Thus the occurrence refinement machinery chooses one ideal
per ambient chart, even when several source opens have the same target.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  (B : κ → Type u) [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]

/-- Each source and each literal overlap contributes one ambient algebra. -/
abbrev PrincipalOccurrenceAmbient : ι ⊕ κ → Type u := Sum.elim A B

instance principalOccurrenceAmbientCommRing (i : ι ⊕ κ) :
    CommRing (PrincipalOccurrenceAmbient A B i) := by
  cases i with
  | inl i => exact inferInstanceAs (CommRing (A i))
  | inr j => exact inferInstanceAs (CommRing (B j))

instance principalOccurrenceAmbientAlgebra (i : ι ⊕ κ) :
    Algebra R (PrincipalOccurrenceAmbient A B i) := by
  cases i with
  | inl i => exact inferInstanceAs (Algebra R (A i))
  | inr j => exact inferInstanceAs (Algebra R (B j))

instance principalOccurrenceAmbientFiniteType (i : ι ⊕ κ) :
    Algebra.FiniteType R (PrincipalOccurrenceAmbient A B i) := by
  cases i with
  | inl i => exact inferInstanceAs (Algebra.FiniteType R (A i))
  | inr j => exact inferInstanceAs (Algebra.FiniteType R (B j))

/-- Source opens remain distinct; an overlap has a single principal occurrence. -/
abbrev PrincipalOccurrenceOpen : ι ⊕ κ → Type z := Sum.elim J (fun _ ↦ PUnit)

instance principalOccurrenceOpenFinite [∀ i, Finite (J i)] (i : ι ⊕ κ) :
    Finite (PrincipalOccurrenceOpen (J := J) i) := by
  cases i with
  | inl i => exact inferInstanceAs (Finite (J i))
  | inr _ => exact inferInstanceAs (Finite PUnit)

/-- The denominator attached to each occurrence of the combined family. -/
def principalOccurrenceAmbientElement (a : ∀ i, J i → A i) (b : ∀ j, B j) :
    ∀ i, PrincipalOccurrenceOpen (J := J) i → PrincipalOccurrenceAmbient A B i
  | .inl i, e => a i e
  | .inr j, _ => b j

/-- Polynomial denominators use the same chosen presentations as the original stages. -/
def principalOccurrenceAmbientRepresentative (a : ∀ i, J i → A i) (b : ∀ j, B j) :
    ∀ i, PrincipalOccurrenceOpen (J := J) i →
      MvPolynomial (Fin (numGenerators R (PrincipalOccurrenceAmbient A B i))) R :=
  fun i e ↦ principalRepresentative R (PrincipalOccurrenceAmbient A B i)
    (principalOccurrenceAmbientElement A B a b i e)

/-- Combine stage bounds without copying any shared overlap relation set. -/
def principalOccurrenceAmbientRelations
    (s : ∀ i, Finset (relationIdeal R (A i)))
    (t : ∀ j, Finset (relationIdeal R (B j))) :
    ∀ i, Finset (relationIdeal R (PrincipalOccurrenceAmbient A B i))
  | .inl i => s i
  | .inr j => t j

/-- The combined bound increases exactly when both constituent families increase. -/
theorem principalOccurrenceAmbientRelations_mono
    {s s' : ∀ i, Finset (relationIdeal R (A i))}
    {t t' : ∀ j, Finset (relationIdeal R (B j))} (hs : s ≤ s') (ht : t ≤ t') :
    principalOccurrenceAmbientRelations A B s t ≤
      principalOccurrenceAmbientRelations A B s' t' := by
  intro i
  cases i with
  | inl i => exact hs i
  | inr j => exact ht j

end FLT.Mazur.FiniteTypeRelationModel
