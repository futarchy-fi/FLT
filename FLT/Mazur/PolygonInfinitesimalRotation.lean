/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicPinchingRotation
public import FLT.Mazur.PolygonInfinitesimalMarkings

/-!
# Rotations of the actual infinitesimal smoothing family

Cyclic translation of the chart indices respects both overlap arrows and thus
descends to the glued scheme. These are actual automorphisms over the original
nilpotent base, carrying every unit marking to its translated label.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing PolygonPinching

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Cyclic translation commutes with the preceding chart index. -/
theorem rotateIndex_preceding (a : ZMod n) (i : Fin n) :
    rotateIndex a ((finRotate n).symm i) = (finRotate n).symm (rotateIndex a i) := by
  apply (ZMod.finEquiv n).injective
  simp [rotateIndex, finRotate_symm_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The translated chart cocone retains the full cyclic overlap relation. -/
def rotationCocone (a : ZMod n) : Cocone (diagram R t n) where
  pt := scheme R t n h
  ι.app j := match j with
    | .left i => leftBranchOpen R t ≫ chart R t n h (rotateIndex a i)
    | .right i => chart R t n h (rotateIndex a i)
  ι.naturality := by
    intro i j f
    cases f with
    | id i => simp
    | fst i => exact (Category.comp_id _).symm
    | snd i =>
      change precedingBranch R t ≫ chart R t n h (rotateIndex a ((finRotate n).symm i)) =
        (leftBranchOpen R t ≫ chart R t n h (rotateIndex a i)) ≫ 𝟙 _
      rw [Category.comp_id, rotateIndex_preceding, overlap]

/-- The actual rotation descended from all the original node charts. -/
def rotation (a : ZMod n) : scheme R t n h ⟶ scheme R t n h :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.desc (diagram R t n) (rotationCocone R t n h a)

/-- On every original chart, rotation is exactly translation of its label. -/
@[reassoc (attr := simp)] theorem chart_rotation (a : ZMod n) (i : Fin n) :
    chart R t n h i ≫ rotation R t n h a = chart R t n h (rotateIndex a i) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.ι_desc (rotationCocone R t n h a) (.right i)

omit [NeZero n] in
/-- Equality of scheme morphisms out of the family can be checked on its node charts. -/
theorem chart_hom_ext {X : Scheme.{u}} {f g : scheme R t n h ⟶ X}
    (hf : ∀ i, chart R t n h i ≫ f = chart R t n h i ≫ g) : f = g := by
  let : Fact (2 ≤ n) := ⟨h⟩
  apply colimit.hom_ext
  intro j
  cases j with
  | right i => exact hf i
  | left i =>
    rw [← colimit.w (diagram R t n) (WalkingMultispan.Hom.fst i)]
    exact (Category.assoc _ _ _).trans ((congrArg (leftBranchOpen R t ≫ ·) (hf i)).trans
      (Category.assoc _ _ _).symm)

/-- Rotation preserves the actual arithmetic structure morphism. -/
@[reassoc (attr := simp)] theorem rotation_toBase (a : ZMod n) :
    rotation R t n h a ≫ toBase R t n h = toBase R t n h := by
  apply chart_hom_ext R t n h
  intro i
  simp

/-- Zero translation gives the identity on the entire family. -/
@[simp] theorem rotation_zero : rotation R t n h 0 = 𝟙 _ := by
  apply chart_hom_ext R t n h
  intro i
  simp

/-- Addition of labels is composition of actual rotations. -/
theorem rotation_add (a b : ZMod n) :
    rotation R t n h (a + b) = rotation R t n h a ≫ rotation R t n h b := by
  apply chart_hom_ext R t n h
  intro i
  simp [rotateIndex_add]

/-- Rotation is invertible over the same nilpotent base. -/
def rotationIso (a : ZMod n) : scheme R t n h ≅ scheme R t n h where
  hom := rotation R t n h a
  inv := rotation R t n h (-a)
  hom_inv_id := by rw [← rotation_add, add_neg_cancel, rotation_zero]
  inv_hom_id := by rw [← rotation_add, neg_add_cancel, rotation_zero]

/-- All the original unit markings transform by the actual cyclic label action. -/
@[reassoc] theorem marking_rotation (a : ZMod n) (i : Fin n) (b : Rˣ) :
    marking R t n h i b ≫ rotation R t n h a =
      marking R t n h (rotateIndex a i) b := by
  simp only [marking, Category.assoc, chart_rotation]

end FLT.Mazur.PolygonInfinitesimal
