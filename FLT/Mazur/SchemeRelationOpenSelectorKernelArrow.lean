/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorCoequalization

/-!
# Constructing original arrows on the assembled scheme kernel

The chart kernels construct local original arrows. Joint monicity of the
original endpoints proves compatibility, so the arrows glue on arbitrary
test schemes with both independent coordinates retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open RelativeRelationOrbit SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] sourceOpen sourceChart
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]
local notation "B" => Scheme.Opens.toScheme (sourceOpen (p := p) (q := q))
local notation "k" => Scheme.Opens.ι (sourceOpen (p := p) (q := q))
variable {Y : Scheme.{u}}

/-- Projection equality makes both coordinates land in a common original chart. -/
theorem kernel_related (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) (z : Y) : Related p q (x z).val (y z).val :=
  related_of_projection_eq e (x z) (y z) (congrArg (fun f ↦ f z) h)

/-- The independent chart coordinates have equal images in their chart quotient. -/
theorem local_kernel_condition (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) (U : Chart p q) :
    firstChart x U ≫ (selector p q U).projection =
      secondChart x y (kernel_related e x y h) U ≫ (selector p q U).projection := by
  apply (cancel_mono (chartMap e U)).mp
  rw [Category.assoc, Category.assoc]
  change firstChart x U ≫ sourceMap e U =
    secondChart x y (kernel_related e x y h) U ≫ sourceMap e U
  rw [← sourceChart_projection, firstChart_source_assoc, secondChart_source_assoc, h]

/-- A full scheme-kernel test constructs an actual original arrow on each chart. -/
def localKernelArrow (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) (U : Chart p q) :
    pullback x (sourceChart U) ⟶ D.left :=
  (selector p q U).kernelLift e (firstChart x U)
    (secondChart x y (kernel_related e x y h) U) (local_kernel_condition e x y h U) ≫
      arrow p.left q.left U.val.val.ι

@[reassoc]
theorem localKernelArrow_fst (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) (U : Chart p q) :
    localKernelArrow e x y h U ≫ p.left = pullback.fst x (sourceChart U) ≫ x ≫ k := by
  rw [localKernelArrow, Category.assoc, arrow_fst,
    SchemeRelationSeedSelector.Data.kernelLift_fst_assoc, firstChart_original]

@[reassoc]
theorem localKernelArrow_snd (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) (U : Chart p q) :
    localKernelArrow e x y h U ≫ q.left = pullback.fst x (sourceChart U) ≫ y ≫ k := by
  rw [localKernelArrow, Category.assoc, arrow_snd,
    SchemeRelationSeedSelector.Data.kernelLift_snd_assoc, secondChart_original]

/-- The original arrows agree on scheme overlaps by original joint monicity. -/
theorem localKernelArrow_compatible (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) (U V : Chart p q) :
    pullback.fst (pullback.fst x (sourceChart U)) (pullback.fst x (sourceChart V)) ≫
      localKernelArrow e x y h U =
      pullback.snd (pullback.fst x (sourceChart U)) (pullback.fst x (sourceChart V)) ≫
      localKernelArrow e x y h V := by
  apply originalArrow_ext e
  · rw [Category.assoc, Category.assoc, localKernelArrow_fst, localKernelArrow_fst,
      ← Category.assoc, ← Category.assoc, pullback.condition]
    simp only [Category.assoc]
  · rw [Category.assoc, Category.assoc, localKernelArrow_snd, localKernelArrow_snd,
      ← Category.assoc, ← Category.assoc, pullback.condition]
    simp only [Category.assoc]

/-- The original arrow is constructed on the entire, possibly nonreduced, test scheme. -/
def kernelArrow (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) : Y ⟶ D.left :=
  (testCover (p := p) (q := q) x).glueMorphisms (localKernelArrow e x y h)
    (localKernelArrow_compatible e x y h)

@[reassoc]
theorem kernelArrow_fst (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) : kernelArrow e x y h ≫ p.left = x ≫ k := by
  apply (testCover (p := p) (q := q) x).hom_ext
  intro U
  rw [← Category.assoc, kernelArrow, Scheme.Cover.ι_glueMorphisms, localKernelArrow_fst]
  rfl

@[reassoc]
theorem kernelArrow_snd (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) : kernelArrow e x y h ≫ q.left = y ≫ k := by
  apply (testCover (p := p) (q := q) x).hom_ext
  intro U
  rw [← Category.assoc, kernelArrow, Scheme.Cover.ι_glueMorphisms, localKernelArrow_snd]
  rfl

end FLT.Mazur.SchemeRelationOpenSelector
