/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAmbientIndex

/-!
# Finite coordinate and restriction edges on the ambient index

Coordinate edges remember their source open and their literal overlap target.
A double-open label remembers an outgoing pair from one source chart; its
second member names the target overlap. Restriction edges start at the first
member's overlap. Empty fibers introduce no artificial arrows.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe v w z

variable {ι : Type v} {κ : Type w} {J : ι → Type z} (dst : ∀ i, J i → κ)

/-- The actual coordinate arrows into one overlap, with their source opens. -/
def PrincipalOccurrenceCoordinateEdge :
    ∀ (_ j : ι ⊕ κ), PrincipalOccurrenceOpen (J := J) j → Type z
  | .inl i, .inr j, _ => {e : J i // dst i e = j}
  | _, _, _ => PEmpty

/-- The occurrence chosen at the source of a coordinate arrow. -/
def principalOccurrenceCoordinateSource :
    ∀ i j o, PrincipalOccurrenceCoordinateEdge dst i j o → PrincipalOccurrenceOpen (J := J) i
  | .inl _, .inr _, _, e => e.val
  | .inl _, .inl _, _, e => e.elim
  | .inr _, .inl _, _, e => e.elim
  | .inr _, .inr _, _, e => e.elim

/-- Double-open labels retain both opens and the literal target equality. -/
def PrincipalOccurrenceDoubleLabel :
    ∀ j : ι ⊕ κ, PrincipalOccurrenceOpen (J := J) j → Type (max v z)
  | .inl _, _ => PEmpty
  | .inr j, _ => {p : Σ i, J i × J i // dst p.1 p.2.2 = j}

/-- Restriction arrows exist precisely from the first overlap in the double-open label. -/
def PrincipalOccurrenceRestrictionEdge :
    ∀ (_ j : ι ⊕ κ) o, PrincipalOccurrenceDoubleLabel dst j o → Type
  | .inr i, .inr _, _, p => PLift (dst p.val.1 p.val.2.1 = i)
  | .inl _, .inr _, _, _ => PEmpty
  | _, .inl _, _, p => p.elim

/-- Restrictions use the single principal occurrence at their source overlap. -/
def principalOccurrenceRestrictionSource :
    ∀ i j o p, PrincipalOccurrenceRestrictionEdge dst i j o p →
      PrincipalOccurrenceOpen (J := J) i
  | .inr _, .inr _, _, _, _ => PUnit.unit
  | .inl _, .inr _, _, _, e => e.elim
  | _, .inl _, _, p, _ => p.elim

variable [Finite ι] [∀ i, Finite (J i)]

instance principalOccurrenceCoordinateEdgeFinite (i j : ι ⊕ κ)
    (o : PrincipalOccurrenceOpen (J := J) j) :
    Finite (PrincipalOccurrenceCoordinateEdge dst i j o) := by
  cases i <;> cases j <;> dsimp [PrincipalOccurrenceCoordinateEdge] <;> infer_instance

instance principalOccurrenceDoubleLabelFinite (j : ι ⊕ κ)
    (o : PrincipalOccurrenceOpen (J := J) j) :
    Finite (PrincipalOccurrenceDoubleLabel dst j o) := by
  cases j <;> dsimp [PrincipalOccurrenceDoubleLabel] <;> infer_instance

instance principalOccurrenceRestrictionEdgeFinite (i j : ι ⊕ κ)
    (o : PrincipalOccurrenceOpen (J := J) j) (p : PrincipalOccurrenceDoubleLabel dst j o) :
    Finite (PrincipalOccurrenceRestrictionEdge dst i j o p) := by
  cases j with
  | inl _ => exact p.elim
  | inr j =>
    cases i <;> dsimp [PrincipalOccurrenceRestrictionEdge] <;> infer_instance

/-- Every original coordinate supplies the corresponding combined-index arrow. -/
def principalOccurrenceCoordinateEdge (i : ι) (e : J i) :
    PrincipalOccurrenceCoordinateEdge dst (.inl i) (.inr (dst i e)) PUnit.unit := ⟨e, rfl⟩

/-- Every pair of source opens supplies the double-open label at its actual target. -/
def principalOccurrenceDoubleLabel (i : ι) (e e' : J i) :
    PrincipalOccurrenceDoubleLabel dst (.inr (dst i e')) PUnit.unit :=
  ⟨⟨i, e, e'⟩, rfl⟩

/-- The restriction from the first overlap has no extra mathematical hypothesis. -/
def principalOccurrenceRestrictionEdge (i : ι) (e e' : J i) :
    PrincipalOccurrenceRestrictionEdge dst (.inr (dst i e)) (.inr (dst i e')) PUnit.unit
      (principalOccurrenceDoubleLabel dst i e e') := ⟨rfl⟩

end FLT.Mazur.FiniteTypeRelationModel
