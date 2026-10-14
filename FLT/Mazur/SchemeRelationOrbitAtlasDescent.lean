/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOrbitAtlas

/-!
# Explicit descent from full orbit relations to full seed relations

An invariant map on the complete orbit descends along its split seed projection.
The descended map is invariant under every original relation between seeds,
including distinct seeds. This does not assert that the seed scheme itself is
the quotient of the full original relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOrbitAtlas
open SchemeRelationRestriction SchemeRelationSplitOrbit
set_option backward.isDefEq.respectTransparency false
variable {S Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (s : Z ⟶ A.left)
local notation "B" => (pullback q.left s : Scheme)
local notation "r" => pullback.fst q.left s
local notation "π" => pullback.snd q.left s
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left s
local notation "σ" => sectionMap e s
local notation "F" => doubleDomain p.left q.left b
local notation "x" => fst p.left q.left b
local notation "y" => snd p.left q.left b
local notation "E" => doubleDomain p.left q.left s
local notation "x₀" => fst p.left q.left s
local notation "y₀" => snd p.left q.left s

/-- Every orbit point is related to the reflexive representative of its own seed. -/
def toSection : B ⟶ F := lift p.left q.left b r (𝟙 B) (π ≫ σ)
  (Category.id_comp _).symm (by
    rw [Category.assoc, sectionMap_source]
    exact pullback.condition)

@[reassoc]
theorem toSection_fst : toSection e s ≫ x = 𝟙 B := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem toSection_snd : toSection e s ≫ y = π ≫ σ := lift_snd _ _ _ _ _ _ _ _

/-- Every full seed arrow lifts using its two independent reflexive representatives. -/
def fromSeeds : E ⟶ F := lift p.left q.left b (arrow p.left q.left s)
  (x₀ ≫ σ) (y₀ ≫ σ)
  (by rw [Category.assoc, sectionMap_source]; exact arrow_fst _ _ _)
  (by rw [Category.assoc, sectionMap_source]; exact arrow_snd _ _ _)

@[reassoc]
theorem fromSeeds_fst : fromSeeds e s ≫ x = x₀ ≫ σ := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem fromSeeds_snd : fromSeeds e s ≫ y = y₀ ≫ σ := lift_snd _ _ _ _ _ _ _ _

/-- Transport every full orbit arrow to an actual relation between its independent seeds. -/
def toSeeds : F ⟶ E := lift p.left q.left s
  (SchemeRelationReanchoring.forwardArrow e r) (x ≫ π) (y ≫ π)
  (by
    rw [SchemeRelationReanchoring.forwardArrow_fst, pullback.condition, Category.assoc]
    rfl)
  (by
    rw [SchemeRelationReanchoring.forwardArrow_snd, pullback.condition, Category.assoc]
    rfl)

@[reassoc]
theorem toSeeds_fst : toSeeds e s ≫ x₀ = x ≫ π := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem toSeeds_snd : toSeeds e s ≫ y₀ = y ≫ π := lift_snd _ _ _ _ _ _ _ _

variable {T : Scheme.{u}}

/-- Descent along the complete orbit is explicit restriction to the reflexive section. -/
def descend (v : B ⟶ T) : Z ⟶ T := σ ≫ v

@[reassoc]
theorem projection_descend (v : B ⟶ T) (hv : x ≫ v = y ≫ v) :
    π ≫ descend e s v = v := by
  have h := congrArg (fun t ↦ toSection e s ≫ t) hv
  simpa only [← Category.assoc, toSection_fst, toSection_snd, Category.id_comp,
    descend] using h.symm

/-- Descent preserves the FULL original seed relation, not only its diagonal. -/
theorem descend_invariant (v : B ⟶ T) (hv : x ≫ v = y ≫ v) :
    x₀ ≫ descend e s v = y₀ ≫ descend e s v := by
  have h := congrArg (fun t ↦ fromSeeds e s ≫ t) hv
  simpa only [← Category.assoc, fromSeeds_fst, fromSeeds_snd, descend] using h

include e in
/-- Pullback of a full seed invariant is a full original-orbit invariant. -/
theorem pull_invariant (v : Z ⟶ T) (hv : x₀ ≫ v = y₀ ≫ v) :
    x ≫ (π ≫ v) = y ≫ (π ≫ v) := by
  have h := congrArg (fun t ↦ toSeeds e s ≫ t) hv
  simpa only [← Category.assoc, toSeeds_fst, toSeeds_snd] using h

/-- Restriction to the section recovers any map on the entire seed scheme. -/
theorem descend_pull (v : Z ⟶ T) : descend e s (π ≫ v) = v := by
  rw [descend, sectionMap_projection_assoc]

/-- Full original invariants and full seed invariants correspond, for arbitrary scheme targets. -/
def invariantEquiv : {v : B ⟶ T // x ≫ v = y ≫ v} ≃
    {v : Z ⟶ T // x₀ ≫ v = y₀ ≫ v} where
  toFun v := ⟨descend e s v.val, descend_invariant e s v.val v.property⟩
  invFun v := ⟨π ≫ v.val, pull_invariant e s v.val v.property⟩
  left_inv v := Subtype.ext (projection_descend e s v.val v.property)
  right_inv v := Subtype.ext (descend_pull e s v.val)

/-- The explicit descent commutes with subsequent scheme and coefficient morphisms. -/
@[reassoc]
theorem descend_comp (v : B ⟶ T) {W : Scheme.{u}} (g : T ⟶ W) :
    descend e s (v ≫ g) = descend e s v ≫ g := (Category.assoc _ _ _).symm

end FLT.Mazur.SchemeRelationOrbitAtlas
