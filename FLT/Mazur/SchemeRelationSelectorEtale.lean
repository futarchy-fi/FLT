/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSelectorKernel
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Etale geometry of constructed representative quotients

The quotient projection is a base change of the original relation endpoint
along the constructed representative inclusion. Thus an etale relation gives
an actual etale surjective quotient, with no flatness input on a coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSelectorQuotient
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (r : A.left ⟶ D.left) (hr : r ≫ p.left = 𝟙 A.left)
  (hi : p.left ≫ r ≫ q.left = q.left ≫ r ≫ q.left)
local notation "v" => projection r hr hi
local notation "i" => inclusion (q := q) r

include hi in
/-- An arrow ending at a fixed representative starts at a point with that representative. -/
theorem representative_of_fixed {Y : Scheme.{u}} (a : Y ⟶ D.left)
    (b : Y ⟶ target (q := q) r) (h : a ≫ q.left = b ≫ i) :
    (a ≫ p.left) ≫ r ≫ q.left = b ≫ i := by
  rw [Category.assoc, hi, ← Category.assoc, h, Category.assoc,
    inclusion_representative]

include e in
/-- The quotient itself is a base change of the original second endpoint. -/
theorem section_isPullback : IsPullback r v q.left i := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (projection_inclusion r hr hi).symm (fun c ↦ c.fst ≫ p.left) ?_ ?_ ?_)
  · intro c
    apply originalArrow_ext e
    · rw [Category.assoc, hr, Category.comp_id]
    · exact (representative_of_fixed r hi c.fst c.snd c.condition).trans c.condition.symm
  · intro c
    apply (cancel_mono i).mp
    rw [Category.assoc, projection_inclusion]
    exact representative_of_fixed r hi c.fst c.snd c.condition
  · intro c a ha _
    have h := congrArg (fun z ↦ z ≫ p.left) ha
    simpa only [Category.assoc, hr, Category.comp_id] using h

include e in
/-- The constructed scheme quotient is etale, proved from the original relation. -/
theorem projection_etale [Etale q.left] : Etale v :=
  MorphismProperty.of_isPullback (section_isPullback e r hr hi) inferInstance

include e in
/-- The full quotient is effective for descent of scheme morphisms. -/
theorem projection_effectiveEpi [Etale q.left] : EffectiveEpi v := by
  let _ := projection_etale e r hr hi
  infer_instance

/-- This is the actual coequalizer of the full original relation. -/
def isColimit [Etale q.left] : IsColimit (Cofork.ofπ v (condition r hr hi)) := by
  let _ := projection_effectiveEpi e r hr hi
  exact isColimitCoforkOfEffectiveEpi v (isPullback e r hr hi).cone
    (isPullback e r hr hi).isLimit

end FLT.Mazur.SchemeRelationSelectorQuotient
