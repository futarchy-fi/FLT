/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedSelector
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Full original kernels of seed representative quotients

Division of original arrows proves the kernel on arbitrary scheme tests.
The quotient projection is a base change of the original etale endpoint
when the seed is etale. Neither a kernel certificate nor flatness is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSeedSelector.Data
open SchemeRelationRestriction RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) {k : B ⟶ A.left} (d : Data p q k)

/-- Quotient equality supplies the common endpoint needed to divide original arrows. -/
theorem representative_eq {Y : Scheme.{u}} (x y : Y ⟶ B)
    (h : x ≫ d.projection = y ≫ d.projection) :
    (x ≫ d.arrow) ≫ q.left = (y ≫ d.arrow) ≫ q.left := by
  have hr : x ≫ d.rep = y ≫ d.rep := by
    simpa only [Category.assoc, projection_inclusion] using
      congrArg (fun a ↦ a ≫ d.inclusion) h
  simpa only [Category.assoc, d.target] using congrArg (fun a ↦ a ≫ k) hr

/-- Recover the full original restricted arrow on every quotient-kernel test. -/
def kernelLift {Y : Scheme.{u}} (x y : Y ⟶ B)
    (h : x ≫ d.projection = y ≫ d.projection) : Y ⟶ doubleDomain p.left q.left k :=
  lift p.left q.left k
    (divideOriginal e (x ≫ d.arrow) (y ≫ d.arrow) (d.representative_eq x y h)) x y
    (by rw [divideOriginal_fst, Category.assoc, d.source])
    (by rw [divideOriginal_snd, Category.assoc, d.source])

@[reassoc]
theorem kernelLift_fst {Y : Scheme.{u}} (x y : Y ⟶ B)
    (h : x ≫ d.projection = y ≫ d.projection) :
    d.kernelLift e x y h ≫ fst p.left q.left k = x := lift_fst ..

@[reassoc]
theorem kernelLift_snd {Y : Scheme.{u}} (x y : Y ⟶ B)
    (h : x ≫ d.projection = y ≫ d.projection) :
    d.kernelLift e x y h ≫ snd p.left q.left k = y := lift_snd ..

include e in
/-- The FULL original seed relation, including nonreduced tests, is the kernel. -/
theorem isPullback : IsPullback (fst p.left q.left k) (snd p.left q.left k)
    d.projection d.projection := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk d.condition
    (fun c ↦ d.kernelLift e c.fst c.snd c.condition)
    (fun c ↦ d.kernelLift_fst e c.fst c.snd c.condition)
    (fun c ↦ d.kernelLift_snd e c.fst c.snd c.condition) ?_)
  intro c a ha hb
  apply SchemeRelationReanchoring.endpoint_ext e k
  · exact ha.trans (d.kernelLift_fst e c.fst c.snd c.condition).symm
  · exact hb.trans (d.kernelLift_snd e c.fst c.snd c.condition).symm

/-- The representative arrow defines a section into the full original seed relation. -/
def sectionArrow : B ⟶ doubleDomain p.left q.left k :=
  lift p.left q.left k d.arrow (𝟙 B) d.rep
    (by simpa only [Category.id_comp] using d.source) d.target

@[reassoc]
theorem sectionArrow_fst : d.sectionArrow ≫ fst p.left q.left k = 𝟙 B := lift_fst ..

@[reassoc]
theorem sectionArrow_snd : d.sectionArrow ≫ snd p.left q.left k = d.rep := lift_snd ..

attribute [local irreducible] sectionArrow projection quotient

include e in
/-- The projection is the base change of the second full relation endpoint at fixed points. -/
theorem section_isPullback : IsPullback d.sectionArrow d.projection
    (snd p.left q.left k) d.inclusion := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by rw [sectionArrow_snd, projection_inclusion])
    (fun c ↦ c.fst ≫ fst p.left q.left k) ?_ ?_ ?_)
  · intro c
    apply SchemeRelationReanchoring.endpoint_ext e k
    · simp only [Category.assoc, sectionArrow_fst, Category.comp_id]
    · simp only [Category.assoc, sectionArrow_snd]
      rw [d.invariant, ← Category.assoc, c.condition, Category.assoc, inclusion_rep]
  · intro c
    apply (cancel_mono d.inclusion).mp
    rw [Category.assoc, projection_inclusion, Category.assoc, d.invariant,
      ← Category.assoc, c.condition, Category.assoc, inclusion_rep]
  · intro c a ha _
    have h := congrArg (fun z ↦ z ≫ fst p.left q.left k) ha
    simpa only [Category.assoc, sectionArrow_fst, Category.comp_id] using h

include e in
/-- Etaleness is proved from the original endpoint and seed geometry. -/
theorem projection_etale [Etale q.left] [Etale k] : Etale d.projection := by
  let _ : Etale (snd p.left q.left k) := by
    unfold snd
    infer_instance
  exact MorphismProperty.of_isPullback (d.section_isPullback e) inferInstance

/-- This constructed scheme is the effective coequalizer of the full seed relation. -/
def isColimit [Etale q.left] [Etale k] :
    IsColimit (Cofork.ofπ d.projection d.condition) := by
  let _ := d.projection_etale e
  exact isColimitCoforkOfEffectiveEpi d.projection (d.isPullback e).cone
    (d.isPullback e).isLimit

end FLT.Mazur.SchemeRelationSeedSelector.Data
