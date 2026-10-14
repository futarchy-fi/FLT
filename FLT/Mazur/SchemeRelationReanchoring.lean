/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationArrowTransport
public import FLT.Mazur.SchemeRelationOverRestriction

/-!
# Reanchoring a full original relation without identifying the seeds

A family of original arrows identifies the full relation on its sources with
the full relation on its targets. Both independent parameters are retained.
This is a scheme isomorphism, not a replacement by the same-seed kernel.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationReanchoring
open SchemeRelationRestriction RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S B : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- The two lifted endpoints determine an arrow in the complete restricted relation. -/
theorem endpoint_ext (k : B ⟶ A.left) {Y : Scheme.{u}}
    {x y : Y ⟶ doubleDomain p.left q.left k}
    (hx : x ≫ fst p.left q.left k = y ≫ fst p.left q.left k)
    (hy : x ≫ snd p.left q.left k = y ≫ snd p.left q.left k) : x = y := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply originalArrow_ext e (a := x ≫ arrow p.left q.left k)
        (b := y ≫ arrow p.left q.left k)
      · simpa only [Category.assoc, arrow_fst] using congrArg (fun t ↦ t ≫ k) hx
      · simpa only [Category.assoc, arrow_snd] using congrArg (fun t ↦ t ≫ k) hy
    · exact hx
  · exact hy

variable (r : B ⟶ D.left)
local notation "b" => r ≫ p.left
local notation "a" => r ≫ q.left
local notation "F" => doubleDomain p.left q.left b
local notation "G" => doubleDomain p.left q.left a
local notation "x" => fst p.left q.left b
local notation "y" => snd p.left q.left b
local notation "z" => arrow p.left q.left b
local notation "x'" => fst p.left q.left a
local notation "y'" => snd p.left q.left a
local notation "z'" => arrow p.left q.left a

/-- Transport the literal original arrow from its source pair to its independent target pair. -/
def forwardArrow : F ⟶ D.left :=
  transportOriginal e (x ≫ r) (y ≫ r) z
    (by simpa only [Category.assoc] using arrow_fst p.left q.left b)
    (by simpa only [Category.assoc] using arrow_snd p.left q.left b)

@[reassoc]
theorem forwardArrow_fst : forwardArrow e r ≫ p.left = x ≫ a := by
  exact (transportOriginal_fst e _ _ _ _ _).trans (Category.assoc _ _ _)

@[reassoc]
theorem forwardArrow_snd : forwardArrow e r ≫ q.left = y ≫ a := by
  exact (transportOriginal_snd e _ _ _ _ _).trans (Category.assoc _ _ _)

/-- The forward map retains both parameters; their seed coordinates may differ. -/
def forward : F ⟶ G := lift p.left q.left a (forwardArrow e r) x y
  (forwardArrow_fst e r) (forwardArrow_snd e r)

@[reassoc]
theorem forward_fst : forward e r ≫ x' = x := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem forward_snd : forward e r ≫ y' = y := lift_snd _ _ _ _ _ _ _ _

@[reassoc]
theorem forward_arrow : forward e r ≫ z' = forwardArrow e r :=
  lift_arrow _ _ _ _ _ _ _ _

/-- Recover the original source relation arrow from the full target relation. -/
def backwardArrow : G ⟶ D.left :=
  untransportOriginal e (x' ≫ r) (y' ≫ r) z'
    (by simpa only [Category.assoc] using arrow_fst p.left q.left a)
    (by simpa only [Category.assoc] using arrow_snd p.left q.left a)

@[reassoc]
theorem backwardArrow_fst : backwardArrow e r ≫ p.left = x' ≫ b := by
  exact (untransportOriginal_fst e _ _ _ _ _).trans (Category.assoc _ _ _)

@[reassoc]
theorem backwardArrow_snd : backwardArrow e r ≫ q.left = y' ≫ b := by
  exact (untransportOriginal_snd e _ _ _ _ _).trans (Category.assoc _ _ _)

/-- Recovery also retains both independent parameter coordinates. -/
def backward : G ⟶ F := lift p.left q.left b (backwardArrow e r) x' y'
  (backwardArrow_fst e r) (backwardArrow_snd e r)

@[reassoc]
theorem backward_fst : backward e r ≫ x = x' := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem backward_snd : backward e r ≫ y = y' := lift_snd _ _ _ _ _ _ _ _

@[reassoc]
theorem backward_arrow : backward e r ≫ z = backwardArrow e r :=
  lift_arrow _ _ _ _ _ _ _ _

/-- The complete relations are isomorphic as schemes with their two endpoint maps. -/
def relationIso : F ≅ G where
  hom := forward e r
  inv := backward e r
  hom_inv_id := by
    apply endpoint_ext e b
    · rw [Category.assoc, backward_fst, forward_fst, Category.id_comp]
    · rw [Category.assoc, backward_snd, forward_snd, Category.id_comp]
  inv_hom_id := by
    apply endpoint_ext e a
    · rw [Category.assoc, forward_fst, backward_fst, Category.id_comp]
    · rw [Category.assoc, forward_snd, backward_snd, Category.id_comp]

include e in
/-- Invariance on the full source relation is equivalent to invariance on the full seed relation. -/
theorem invariant_iff {T : Scheme.{u}} (v : B ⟶ T) :
    x ≫ v = y ≫ v ↔ x' ≫ v = y' ≫ v := by
  constructor
  · intro h
    simpa only [← Category.assoc, backward_fst, backward_snd] using
      congrArg (fun t ↦ backward e r ≫ t) h
  · intro h
    simpa only [← Category.assoc, forward_fst, forward_snd] using
      congrArg (fun t ↦ forward e r ≫ t) h

end FLT.Mazur.SchemeRelationReanchoring
