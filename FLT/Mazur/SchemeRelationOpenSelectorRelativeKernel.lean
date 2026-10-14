/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorKernel

/-!
# The full assembled relation over the original ground

The relation object is the actual full double restriction of the original
arrows. Its two original source coordinates and the assembled quotient retain
the unchanged ground morphism throughout the kernel identification.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] sourceOpen projection glued
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
local notation "k" => Scheme.Opens.ι (sourceOpen (p := p) (q := q))

/-- The original source union with its unchanged ground morphism. -/
def relativeSource : Over S := Over.mk (k ≫ A.hom)

/-- The full original relation with the ground map inherited from its original arrows. -/
def relativeRelation : Over S := Over.mk (arrow p.left q.left k ≫ D.hom)

/-- First endpoint of the actual original relation, over the unchanged ground. -/
def relativeFst : relativeRelation (p := p) (q := q) ⟶ relativeSource (p := p) (q := q) :=
  Over.homMk (fst p.left q.left k) (by
    change fst p.left q.left k ≫ (k ≫ A.hom) = arrow p.left q.left k ≫ D.hom
    rw [← Category.assoc, ← arrow_fst, Category.assoc, p.w])

/-- Independent second endpoint of the same original relation. -/
def relativeSnd : relativeRelation (p := p) (q := q) ⟶ relativeSource (p := p) (q := q) :=
  Over.homMk (snd p.left q.left k) (by
    change snd p.left q.left k ≫ (k ≫ A.hom) = arrow p.left q.left k ≫ D.hom
    rw [← Category.assoc, ← arrow_snd, Category.assoc, q.w])

/-- Forgetting the restricted relation keeps the original scheme arrow. -/
def relativeArrow : relativeRelation (p := p) (q := q) ⟶ D :=
  Over.homMk (arrow p.left q.left k)

/-- Inclusion of the original source union as a relative scheme. -/
def relativeSourceInclusion : relativeSource (p := p) (q := q) ⟶ A := Over.homMk k

@[reassoc]
theorem relativeArrow_fst : relativeArrow (p := p) (q := q) ≫ p =
    relativeFst (p := p) (q := q) ≫ relativeSourceInclusion :=
  Over.OverMorphism.ext (arrow_fst p.left q.left k)

@[reassoc]
theorem relativeArrow_snd : relativeArrow (p := p) (q := q) ≫ q =
    relativeSnd (p := p) (q := q) ≫ relativeSourceInclusion :=
  Over.OverMorphism.ext (arrow_snd p.left q.left k)

variable (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]

/-- The complete scheme-kernel identification also holds over the original ground. -/
theorem relative_isPullback : IsPullback (relativeFst (p := p) (q := q)) relativeSnd
    (relativeProjection e) (relativeProjection e) :=
  IsPullback.of_map_of_faithful (Over.forget S) (projection_isPullback e)

/-- The full original restricted arrows carry their constructed equivalence relation. -/
def relativeEquivalence :
    CategoryTheory.EquivalenceRelation (relativeFst (p := p) (q := q)) relativeSnd :=
  IsKernelPair.equivalenceRelation (relativeProjection e) _ _
    (pullback.isLimit _ _) (relative_isPullback e)

end FLT.Mazur.SchemeRelationOpenSelector
