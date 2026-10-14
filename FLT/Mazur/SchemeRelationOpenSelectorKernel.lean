/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorKernelArrow

/-!
# The full original kernel of the assembled selector quotient

The locally constructed original arrows give the universal lift of the full
two-coordinate restriction. Etale surjectivity then proves effectiveness of
the actual quotient scheme, without assuming any global representative.
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
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]
local notation "B" => Scheme.Opens.toScheme (sourceOpen (p := p) (q := q))
local notation "k" => Scheme.Opens.ι (sourceOpen (p := p) (q := q))

/-- Construct the complete original restricted arrow of a kernel test. -/
def kernelLift {Y : Scheme.{u}} (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) : Y ⟶ doubleDomain p.left q.left k :=
  lift p.left q.left k (kernelArrow e x y h) x y
    (kernelArrow_fst e x y h) (kernelArrow_snd e x y h)

@[reassoc]
theorem kernelLift_fst {Y : Scheme.{u}} (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) :
    kernelLift e x y h ≫ fst p.left q.left k = x := lift_fst ..

@[reassoc]
theorem kernelLift_snd {Y : Scheme.{u}} (x y : Y ⟶ B)
    (h : x ≫ projection e = y ≫ projection e) :
    kernelLift e x y h ≫ snd p.left q.left k = y := lift_snd ..

/-- The assembled projection has precisely the FULL original restricted scheme kernel. -/
theorem projection_isPullback : IsPullback (fst p.left q.left k) (snd p.left q.left k)
    (projection e) (projection e) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (projection_condition e)
    (fun c ↦ kernelLift e c.fst c.snd c.condition)
    (fun c ↦ kernelLift_fst e c.fst c.snd c.condition)
    (fun c ↦ kernelLift_snd e c.fst c.snd c.condition) ?_)
  intro c a ha hb
  apply SchemeRelationReanchoring.endpoint_ext e k
  · exact ha.trans (kernelLift_fst e c.fst c.snd c.condition).symm
  · exact hb.trans (kernelLift_snd e c.fst c.snd c.condition).symm

/-- An explicit scheme isomorphism identifies the original full relation and the kernel pair. -/
def kernelIso : doubleDomain p.left q.left k ≅ pullback (projection e) (projection e) :=
  (projection_isPullback e).isoPullback

/-- The glued scheme is the effective coequalizer of its full original restricted relation. -/
def isColimit : IsColimit (Cofork.ofπ (projection e) (projection_condition e)) := by
  let _ := projection_etale e
  let _ := projection_surjective e
  exact isColimitCoforkOfEffectiveEpi (projection e) (projection_isPullback e).cone
    (projection_isPullback e).isLimit

/-- The constructed projection remains a cover after every scheme base change. -/
theorem projection_baseChange_cover {T : Scheme.{u}} (v : T ⟶ glued e) :
    Etale (pullback.snd (projection e) v) ∧ Surjective (pullback.snd (projection e) v) := by
  let _ := projection_etale e
  let _ := projection_surjective e
  exact ⟨inferInstance, inferInstance⟩

end FLT.Mazur.SchemeRelationOpenSelector
