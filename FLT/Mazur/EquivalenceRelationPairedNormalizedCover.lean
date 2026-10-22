/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationExactRankNormalizedCover

/-!
# Simultaneous normalized frames over the unchanged coefficient scheme

Two successive pullbacks construct both normalized endpoint lifts. Exact ranks
make their common projection an etale surjection. The ranks may differ; equality
of original scalar characters alone is not used to identify them.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (n m : ℕ) (o : Fin n) (j : Fin m) (x y : B ⟶ A)
attribute [local irreducible] source

/-- The actual common coefficient extension carrying the two independent normalized frames. -/
def pairedNormalizedCover : Scheme :=
  exactNormalizedCover (p := p) (q := q) m j
    (exactNormalizedProjection (p := p) (q := q) n o x ≫ y)

/-- Project both frame choices to the original coefficient scheme. -/
def pairedNormalizedProjection :
    pairedNormalizedCover (p := p) (q := q) n m o j x y ⟶ B :=
  exactNormalizedProjection (p := p) (q := q) m j
    (exactNormalizedProjection (p := p) (q := q) n o x ≫ y) ≫
      exactNormalizedProjection (p := p) (q := q) n o x

/-- The first endpoint lift retains the original first normalized frame. -/
def pairedNormalizedFirst :
    pairedNormalizedCover (p := p) (q := q) n m o j x y ⟶
      source p q (Fin n) o :=
  exactNormalizedProjection (p := p) (q := q) m j
    (exactNormalizedProjection (p := p) (q := q) n o x ≫ y) ≫
      exactNormalizedFrame (p := p) (q := q) n o x

/-- The second endpoint lift is the tautological frame of the second pullback. -/
def pairedNormalizedSecond :
    pairedNormalizedCover (p := p) (q := q) n m o j x y ⟶
      source p q (Fin m) j :=
  exactNormalizedFrame (p := p) (q := q) m j
    (exactNormalizedProjection (p := p) (q := q) n o x ≫ y)

/-- The first lifted endpoint is the prescribed first endpoint on the entire cover. -/
@[reassoc] theorem pairedNormalizedFirst_endpoint :
    pairedNormalizedFirst (p := p) (q := q) n m o j x y ≫ first p q (Fin n) o =
      pairedNormalizedProjection (p := p) (q := q) n m o j x y ≫ x := by
  simp only [pairedNormalizedFirst, pairedNormalizedProjection, Category.assoc,
    exactNormalizedFrame_first]

/-- The second lifted endpoint is independently retained as a scheme morphism. -/
@[reassoc] theorem pairedNormalizedSecond_endpoint :
    pairedNormalizedSecond (p := p) (q := q) n m o j x y ≫ first p q (Fin m) j =
      pairedNormalizedProjection (p := p) (q := q) n m o j x y ≫ y := by
  exact (exactNormalizedFrame_first m j _).trans (Category.assoc _ _ _).symm

variable [Etale p] [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
local instance pairCoverOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance pairCoverOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance pairCoverOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
omit [QuasiCompact p] in
/-- The simultaneous extension is etale over the unchanged coefficient scheme. -/
theorem pairedNormalizedProjection_etale :
    Etale (pairedNormalizedProjection (p := p) (q := q) n m o j x y) := by
  let _ := exactNormalizedProjection_etale e n o x
  let _ := exactNormalizedProjection_etale e m j
    (exactNormalizedProjection (p := p) (q := q) n o x ≫ y)
  unfold pairedNormalizedProjection
  infer_instance

include e in
/-- Both full exact rank hypotheses give actual simultaneous coverage, without reduction. -/
theorem pairedNormalizedProjection_surjective
    (hx : Set.range x ⊆ exactRank (Over.mk p) n)
    (hy : Set.range y ⊆ exactRank (Over.mk p) m) :
    Function.Surjective (pairedNormalizedProjection (p := p) (q := q) n m o j x y) := by
  have h₁ := exactNormalizedProjection_surjective e n o x hx
  have h₂ := exactNormalizedProjection_surjective e m j
    (exactNormalizedProjection (p := p) (q := q) n o x ≫ y) (by
      rintro _ ⟨z, rfl⟩
      exact hy (Set.mem_range_self _))
  exact h₁.comp h₂

end FLT.Mazur.EquivalenceRelationNormalizedFrames
