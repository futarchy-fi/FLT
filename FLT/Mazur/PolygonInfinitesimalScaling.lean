/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingScalingBranches
public import FLT.Mazur.PolygonInfinitesimalRotation

/-!
# Scaling automorphisms on the entire original infinitesimal polygon

Reciprocal scaling glues on all original node charts over a nilpotent base.
The resulting whole-scheme automorphisms retain the base and all unit markings,
and commute with cyclic rotation. No extension to the complete family is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The scaled original arithmetic charts form a cocone on both full branch overlaps. -/
def scalingCocone (a : Rˣ) : Cocone (diagram R t n) where
  pt := scheme R t n h
  ι.app j := match j with
    | .left i => (edgeScalingIso a).hom ≫ leftBranchOpen R t ≫ chart R t n h i
    | .right i => (reciprocalScalingIso t a).hom ≫ chart R t n h i
  ι.naturality := by
    intro i j f
    cases f with
    | id i => simp
    | fst i =>
      change leftBranchOpen R t ≫ ((reciprocalScalingIso t a).hom ≫ chart R t n h i) =
        ((edgeScalingIso a).hom ≫ leftBranchOpen R t ≫ chart R t n h i) ≫ 𝟙 _
      rw [leftBranch_reciprocalScaling_assoc, Category.comp_id]
    | snd i =>
      change precedingBranch R t ≫ ((reciprocalScalingIso t a).hom ≫
        chart R t n h ((finRotate n).symm i)) =
        ((edgeScalingIso a).hom ≫ leftBranchOpen R t ≫ chart R t n h i) ≫ 𝟙 _
      rw [precedingBranch_reciprocalScaling_assoc, overlap, Category.comp_id]

/-- An actual automorphism map on the whole original infinitesimal polygon. -/
def scaling (a : Rˣ) : scheme R t n h ⟶ scheme R t n h :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimit.desc (diagram R t n) (scalingCocone R t n h a)

/-- Every original arithmetic node chart retains exactly its constructed scaling. -/
@[reassoc (attr := simp)] theorem chart_scaling (a : Rˣ) (i : Fin n) :
    chart R t n h i ≫ scaling R t n h a =
      (reciprocalScalingIso t a).hom ≫ chart R t n h i := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact colimit.ι_desc (scalingCocone R t n h a) (.right i)

/-- The whole original infinitesimal polygon stays over its original coefficient base. -/
@[reassoc] theorem scaling_toBase (a : Rˣ) :
    scaling R t n h a ≫ toBase R t n h = toBase R t n h := by
  apply chart_hom_ext R t n h
  intro i
  simp only [chart_scaling_assoc, chart_toBase, reciprocalScalingIso_base]

/-- The unit scaling is the identity on the entire original infinitesimal polygon. -/
@[simp] theorem scaling_one : scaling R t n h 1 = 𝟙 _ := by
  apply chart_hom_ext R t n h
  intro i
  simp

/-- Multiplication of units is composition of the actual whole-polygon maps. -/
theorem scaling_mul (a b : Rˣ) :
    scaling R t n h (a * b) = scaling R t n h a ≫ scaling R t n h b := by
  apply chart_hom_ext R t n h
  intro i
  simp only [chart_scaling, chart_scaling_assoc, reciprocalScalingIso_mul, Category.assoc]

/-- Reciprocal coefficient units give the inverse on every original component and node. -/
def scalingIso (a : Rˣ) : scheme R t n h ≅ scheme R t n h where
  hom := scaling R t n h a
  inv := scaling R t n h a⁻¹
  hom_inv_id := by rw [← scaling_mul, mul_inv_cancel, scaling_one]
  inv_hom_id := by rw [← scaling_mul, inv_mul_cancel, scaling_one]

/-- Scaling carries every original unit marking to the multiplied unit marking. -/
@[reassoc] theorem marking_scaling (a b : Rˣ) (i : Fin n) :
    marking R t n h i b ≫ scaling R t n h a = marking R t n h i (a * b) := by
  rw [marking, Category.assoc, chart_scaling, ← Category.assoc,
    markedSection_reciprocalScaling, marking]

variable [NeZero n]

/-- The constructed whole-polygon scaling commutes with all original cyclic rotations. -/
theorem scaling_rotation (a : Rˣ) (b : ZMod n) :
    scaling R t n h a ≫ rotation R t n h b = rotation R t n h b ≫ scaling R t n h a := by
  apply chart_hom_ext R t n h
  intro i
  simp only [chart_scaling_assoc, chart_rotation_assoc, chart_rotation, chart_scaling]

end FLT.Mazur.PolygonInfinitesimal
