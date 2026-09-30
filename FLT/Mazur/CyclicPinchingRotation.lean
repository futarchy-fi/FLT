/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPinchingDiagram
public import Mathlib.Data.ZMod.Basic

/-!
# Rotations of the cyclic pinching span

Translation in `ZMod n` permutes the normalization components and nodes, and
permutes branches without changing their endpoint label. The cyclic successor
commutes with translation, so these maps preserve both legs of the span in
DR II.1.1, including the one-component case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonPinching

variable {n : ℕ} [NeZero n]

/-- Rotate the component index by a residue class. -/
def rotateIndex (a : ZMod n) (i : Fin n) : Fin n :=
  (ZMod.finEquiv n).symm (ZMod.finEquiv n i + a)

@[simp]
theorem rotateIndex_zero (i : Fin n) : rotateIndex 0 i = i := by
  simp [rotateIndex]

theorem rotateIndex_add (a b : ZMod n) (i : Fin n) :
    rotateIndex (a + b) i = rotateIndex b (rotateIndex a i) := by
  simp [rotateIndex, add_assoc]

/-- The successor is addition by one in the finite ring. -/
theorem next_eq_add_one (hn : 0 < n) (i : Fin n) : next hn i = i + 1 := by
  apply Fin.ext
  simp [next, Fin.val_add, Nat.add_mod]

/-- Rotation respects the infinity branch's successor component. -/
theorem rotateIndex_next (hn : 0 < n) (a : ZMod n) (i : Fin n) :
    rotateIndex a (next hn i) = next hn (rotateIndex a i) := by
  apply (ZMod.finEquiv n).injective
  simp [rotateIndex, next_eq_add_one, add_assoc, add_comm, add_left_comm]

@[simp]
theorem rotateIndex_one (a : ZMod 1) (i : Fin 1) : rotateIndex a i = i :=
  Subsingleton.elim _ _

variable (K : Type u) [Field K]

/-- Rotation of the normalization components. -/
def componentsRotation (a : ZMod n) : components K n ⟶ components K n :=
  Sigma.desc fun i ↦ componentι K n (rotateIndex a i)

/-- Rotation of branches, preserving the zero/infinity label. -/
def branchesRotation (a : ZMod n) : branches K n ⟶ branches K n :=
  Sigma.desc fun ib ↦ branchι K n (rotateIndex a ib.1) ib.2

/-- Rotation of the nodes. -/
def nodesRotation (a : ZMod n) : nodes K n ⟶ nodes K n :=
  Sigma.desc fun i ↦ nodeι K n (rotateIndex a i)

@[reassoc (attr := simp)]
theorem componentι_rotation (a : ZMod n) (i : Fin n) :
    componentι K n i ≫ componentsRotation K a = componentι K n (rotateIndex a i) := by
  simp [componentι, componentsRotation]

@[reassoc (attr := simp)]
theorem branchι_rotation (a : ZMod n) (i : Fin n) (b : Bool) :
    branchι K n i b ≫ branchesRotation K a = branchι K n (rotateIndex a i) b := by
  simp [branchι, branchesRotation]

@[reassoc (attr := simp)]
theorem nodeι_rotation (a : ZMod n) (i : Fin n) :
    nodeι K n i ≫ nodesRotation K a = nodeι K n (rotateIndex a i) := by
  simp [nodeι, nodesRotation]

/-- Rotation preserves the normalization leg of the span. -/
theorem rotation_toComponents (hn : 0 < n) (a : ZMod n) :
    branchesRotation K a ≫ toComponents K n hn =
      toComponents K n hn ≫ componentsRotation K a := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  cases b <;> simp [rotateIndex_next]

/-- Rotation preserves the node leg of the span. -/
theorem rotation_toNodes (a : ZMod n) :
    branchesRotation K a ≫ toNodes K n = toNodes K n ≫ nodesRotation K a := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  simp

@[simp]
theorem componentsRotation_zero : componentsRotation K (0 : ZMod n) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp

@[simp]
theorem branchesRotation_zero : branchesRotation K (0 : ZMod n) = 𝟙 _ := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change branchι K n i b ≫ _ = branchι K n i b ≫ _
  simp

@[simp]
theorem nodesRotation_zero : nodesRotation K (0 : ZMod n) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  change nodeι K n i ≫ _ = nodeι K n i ≫ _
  simp

theorem componentsRotation_add (a b : ZMod n) :
    componentsRotation K (a + b) = componentsRotation K a ≫ componentsRotation K b := by
  apply Sigma.hom_ext
  intro i
  change componentι K n i ≫ _ = componentι K n i ≫ _
  simp [rotateIndex_add]

theorem branchesRotation_add (a b : ZMod n) :
    branchesRotation K (a + b) = branchesRotation K a ≫ branchesRotation K b := by
  apply Sigma.hom_ext
  rintro ⟨i, c⟩
  change branchι K n i c ≫ _ = branchι K n i c ≫ _
  simp [rotateIndex_add]

theorem nodesRotation_add (a b : ZMod n) :
    nodesRotation K (a + b) = nodesRotation K a ≫ nodesRotation K b := by
  apply Sigma.hom_ext
  intro i
  change nodeι K n i ≫ _ = nodeι K n i ≫ _
  simp [rotateIndex_add]

end FLT.Mazur.PolygonPinching
