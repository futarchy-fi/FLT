/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCommonPrincipalCover

/-!
# Finite occurrence data from an arbitrary affine atlas

Each ordered pair of charts has a selected finite common principal cover.
Every selected overlap occurs in both ambient charts, retaining a literal
shared label even when the two ambient chart indices coincide.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {X : Scheme.{u}} [QuasiSeparatedSpace X] {ι : Type v} (U : ι → X.affineOpens)

/-- The chosen finite common principal cover of a pair of affine charts. -/
def atlasPrincipalPairs (i j : ι) : Finset (Γ(X, (U i).1) × Γ(X, (U j).1)) :=
  (exists_finite_common_principal_cover_of_quasiSeparated (U i).2 (U j).2).choose

/-- Both functions define the same actual open subscheme. -/
theorem atlasPrincipalPairs_eq (i j : ι) (p : atlasPrincipalPairs U i j) :
    X.basicOpen p.val.1 = X.basicOpen p.val.2 :=
  (exists_finite_common_principal_cover_of_quasiSeparated (U i).2 (U j).2).choose_spec.1
    p.val p.property

/-- The selected overlaps cover the full intersection, including self-intersections. -/
theorem atlasPrincipalPairs_cover (i j : ι) :
    (⨆ p : atlasPrincipalPairs U i j, X.basicOpen p.val.1) = (U i).1 ⊓ (U j).1 :=
  (exists_finite_common_principal_cover_of_quasiSeparated (U i).2 (U j).2).choose_spec.2

/-- A literal overlap label records its pair of charts and chosen common open. -/
abbrev AtlasPrincipalOverlap := Σ i, Σ j, atlasPrincipalPairs U i j

/-- Occurrences in a chart remember which side of an ordered pair they come from. -/
abbrev AtlasPrincipalOccurrence (i : ι) :=
  Σ j, atlasPrincipalPairs U i j ⊕ atlasPrincipalPairs U j i

/-- Every occurrence refers to exactly one shared overlap label. -/
def atlasPrincipalDestination (i : ι) : AtlasPrincipalOccurrence U i → AtlasPrincipalOverlap U
  | ⟨j, .inl p⟩ => ⟨i, j, p⟩
  | ⟨j, .inr p⟩ => ⟨j, i, p⟩

/-- The function cutting out an occurrence in its own ambient chart. -/
def atlasPrincipalSection (i : ι) : AtlasPrincipalOccurrence U i → Γ(X, (U i).1)
  | ⟨_, .inl p⟩ => p.val.1
  | ⟨_, .inr p⟩ => p.val.2

/-- The shared overlap is the actual common principal open, viewed as an affine open. -/
def atlasPrincipalOpen (k : AtlasPrincipalOverlap U) : X.affineOpens :=
  ⟨X.basicOpen k.2.2.val.1, (U k.1).2.basicOpen _⟩

/-- Both occurrences recover the literal shared open. -/
theorem atlasPrincipalSection_open (i : ι) (k : AtlasPrincipalOccurrence U i) :
    X.basicOpen (atlasPrincipalSection U i k) =
      (atlasPrincipalOpen U (atlasPrincipalDestination U i k)).1 := by
  obtain ⟨j, p | p⟩ := k
  · rfl
  · exact (atlasPrincipalPairs_eq U j i p).symm

/-- The chosen overlap lies in its first chart. -/
theorem atlasPrincipalOpen_le_left (k : AtlasPrincipalOverlap U) :
    (atlasPrincipalOpen U k).1 ≤ (U k.1).1 := X.basicOpen_le _

/-- The chosen overlap also lies in its second chart. -/
theorem atlasPrincipalOpen_le_right (k : AtlasPrincipalOverlap U) :
    (atlasPrincipalOpen U k).1 ≤ (U k.2.1).1 := by
  change X.basicOpen k.2.2.val.1 ≤ _
  rw [atlasPrincipalPairs_eq]
  exact X.basicOpen_le _

/-- A finite affine atlas produces finitely many literal overlap labels. -/
instance atlasPrincipalOverlap_finite [Finite ι] : Finite (AtlasPrincipalOverlap U) :=
  inferInstance

/-- Every ambient chart has only finitely many occurrences. -/
instance atlasPrincipalOccurrence_finite [Finite ι] (i : ι) :
    Finite (AtlasPrincipalOccurrence U i) := inferInstance

end FLT.Mazur.Approximation
