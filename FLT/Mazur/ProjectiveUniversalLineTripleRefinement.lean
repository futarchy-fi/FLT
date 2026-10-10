/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUniversalLineRefinementWitness
public import FLT.Mazur.ProjectiveUniversalLineTripleComparison

/-!
# The actual universal line cocycle on homogeneous triple overlaps

Each transition below is the pullback of the original pairwise overlap
isomorphism. Canonical geometric comparisons and the proved ring-map path
identities put their endpoints on the same three actual chart pullbacks.
Their composite equals the directly refined outer transition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open NormalizedSectionLine
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original first pairwise transition, pulled back to the actual triple intersection. -/
def universalTripleOverlap₁₂ (i j k : ι) :=
  universalLineRefinement R ι i j (toTriple₁₂ R ι i j k)
    (universalTripleMap₁ R ι i j k) (universalTripleMap₂ R ι i j k) rfl rfl

/-- The original second pairwise transition with its endpoints canonically identified. -/
def universalTripleOverlap₂₃ (i j k : ι) :=
  universalLineRefinement R ι j k (toTriple₂₃ R ι i j k)
    (universalTripleMap₂ R ι i j k) (universalTripleMap₃ R ι i j k)
    (chartTriple_middle R ι i j k).symm rfl

/-- The original outer transition with the same first and last endpoints. -/
def universalTripleOverlap₁₃ (i j k : ι) :=
  universalLineRefinement R ι i k (toTriple₁₃ R ι i j k)
    (universalTripleMap₁ R ι i j k) (universalTripleMap₃ R ι i j k)
    (chartTriple_first R ι i j k).symm (chartTriple_last R ι i j k).symm

attribute [local irreducible] universalLineRefinement universalLineCompare
attribute [local irreducible] Scheme.Modules.pullback

/-- The first refined transition is the comparison of its actual extended submodules. -/
lemma universalTripleOverlap₁₂_eq (i j k : ι) :
    universalTripleOverlap₁₂ R ι i j k =
      universalLineCompare R ι i j (universalTripleMap₁ R ι i j k)
        (universalTripleMap₂ R ι i j k) (universalTripleLine_val₁₂ R ι i j k) :=
  universalLineRefinement_eq R ι i j _ _ _ rfl rfl _

/-- The middle path identity identifies the second refined transition's source. -/
lemma universalTripleOverlap₂₃_eq (i j k : ι) :
    universalTripleOverlap₂₃ R ι i j k =
      universalLineCompare R ι j k (universalTripleMap₂ R ι i j k)
        (universalTripleMap₃ R ι i j k) (universalTripleLine_val₂₃ R ι i j k) :=
  universalLineRefinement_eq R ι j k _ _ _ _ rfl _

/-- The outer path identities identify the directly refined outer transition. -/
lemma universalTripleOverlap₁₃_eq (i j k : ι) :
    universalTripleOverlap₁₃ R ι i j k =
      universalLineCompare R ι i k (universalTripleMap₁ R ι i j k)
        (universalTripleMap₃ R ι i j k) (universalTripleLine_val₁₃ R ι i j k) :=
  universalLineRefinement_eq R ι i k _ _ _ _ _ _

/-- The actual geometric refinements of the universal overlap maps satisfy the triple cocycle. -/
lemma universalTripleOverlap_cocycle [Finite ι] (i j k : ι) :
    universalTripleOverlap₁₂ R ι i j k ≪≫ universalTripleOverlap₂₃ R ι i j k =
      universalTripleOverlap₁₃ R ι i j k := by
  rw [universalTripleOverlap₁₂_eq, universalTripleOverlap₂₃_eq, universalTripleOverlap₁₃_eq]
  exact universalLineCompare_cocycle R ι i j k _ _ _ _ _

/-- The composed forward maps agree on the actual homogeneous triple localization. -/
lemma universalTripleOverlap_hom_cocycle [Finite ι] (i j k : ι) :
    (universalTripleOverlap₁₂ R ι i j k).hom ≫
        (universalTripleOverlap₂₃ R ι i j k).hom =
      (universalTripleOverlap₁₃ R ι i j k).hom :=
  congrArg Iso.hom (universalTripleOverlap_cocycle R ι i j k)

/-- The first refined original overlap retains its actual ambient inclusion. -/
lemma universalTripleOverlap₁₂_inclusion [Finite ι] (i j k : ι) :
    (universalTripleOverlap₁₂ R ι i j k).hom ≫
        universalLinePullbackInclusion R ι j (universalTripleMap₂ R ι i j k) =
      universalLinePullbackInclusion R ι i (universalTripleMap₁ R ι i j k) :=
  universalLineRefinement_inclusion R ι i j _ _ _ _ _

/-- The second refined original overlap retains the same ambient inclusion. -/
lemma universalTripleOverlap₂₃_inclusion [Finite ι] (i j k : ι) :
    (universalTripleOverlap₂₃ R ι i j k).hom ≫
        universalLinePullbackInclusion R ι k (universalTripleMap₃ R ι i j k) =
      universalLinePullbackInclusion R ι j (universalTripleMap₂ R ι i j k) :=
  universalLineRefinement_inclusion R ι j k _ _ _ _ _

/-- The outer refined original overlap retains the same ambient inclusion. -/
lemma universalTripleOverlap₁₃_inclusion [Finite ι] (i j k : ι) :
    (universalTripleOverlap₁₃ R ι i j k).hom ≫
        universalLinePullbackInclusion R ι k (universalTripleMap₃ R ι i j k) =
      universalLinePullbackInclusion R ι i (universalTripleMap₁ R ι i j k) :=
  universalLineRefinement_inclusion R ι i k _ _ _ _ _

end FLT.Mazur.ProjectiveSpace
