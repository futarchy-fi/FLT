/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarRelationPullback
public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Full relation tests from a scalar chart equalizer

A coefficient on a scalar chart tests every original arrow whose endpoints
lift to that chart with the same scalar-test coordinate. The two lifts remain
independent, and the construction retains the entire test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarRelationPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeRelationRestriction.doubleDomain
  SchemeRelationRestriction.fst SchemeRelationRestriction.snd
  SchemeRelationRestriction.lift testFirst testSecond
variable {D X U S Y : Scheme.{0}} (p q : D ⟶ X) (j : U ⟶ X) (s : U ⟶ S)
local notation "F" => SchemeRelationRestriction.fst p q j
local notation "H" => SchemeRelationRestriction.snd p q j
variable (hs : SchemeRelationRestriction.fst p q j ≫ s =
  SchemeRelationRestriction.snd p q j ≫ s) (b : Y ⟶ S)

/-- A full original arrow with independent chart lifts gives a scalar relation test. -/
def restrictedTestLift {T : Scheme.{0}} (w : T ⟶ D)
    (u v : T ⟶ testSource s b)
    (hu : w ≫ p = u ≫ pullback.fst s b ≫ j)
    (hv : w ≫ q = v ≫ pullback.fst s b ≫ j) : T ⟶ testRelation F s b :=
  pullback.lift
    (SchemeRelationRestriction.lift p q j w
      (u ≫ pullback.fst s b) (v ≫ pullback.fst s b)
      (by simpa only [Category.assoc] using hu)
      (by simpa only [Category.assoc] using hv))
    (u ≫ pullback.snd s b) (by
      rw [← Category.assoc, SchemeRelationRestriction.lift_fst]
      simp only [Category.assoc, pullback.condition])

attribute [local irreducible] restrictedTestLift

@[reassoc]
theorem restrictedTestLift_first {T : Scheme.{0}} (w : T ⟶ D)
    (u v : T ⟶ testSource s b)
    (hu : w ≫ p = u ≫ pullback.fst s b ≫ j)
    (hv : w ≫ q = v ≫ pullback.fst s b ≫ j) :
    restrictedTestLift p q j s b w u v hu hv ≫ testFirst F s b = u := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testFirst_fst, restrictedTestLift,
      pullback.lift_fst_assoc, SchemeRelationRestriction.lift_fst]
  · simp only [Category.assoc, testFirst, restrictedTestLift, pullback.lift_snd]

include p q j s hs

@[reassoc]
theorem restrictedTestLift_second {T : Scheme.{0}} (w : T ⟶ D)
    (u v : T ⟶ testSource s b)
    (hu : w ≫ p = u ≫ pullback.fst s b ≫ j)
    (hv : w ≫ q = v ≫ pullback.fst s b ≫ j)
    (hb : u ≫ pullback.snd s b = v ≫ pullback.snd s b) :
    restrictedTestLift p q j s b w u v hu hv ≫ testSecond F H s hs b = v := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testSecond_fst, restrictedTestLift,
      pullback.lift_fst_assoc, SchemeRelationRestriction.lift_snd]
  · simpa only [Category.assoc, testSecond, restrictedTestLift, pullback.lift_snd] using hb

/-- A scalar chart invariant satisfies every full original arrow test over one test point. -/
theorem restricted_invariant_test (a : testInvariants F H s hs b)
    {T : Scheme.{0}} (w : T ⟶ D) (u v : T ⟶ testSource s b)
    (hu : w ≫ p = u ≫ pullback.fst s b ≫ j)
    (hv : w ≫ q = v ≫ pullback.fst s b ≫ j)
    (hb : u ≫ pullback.snd s b = v ≫ pullback.snd s b) :
    u.appTop a.val = v.appTop a.val := by
  have h := congrArg (fun z ↦ (restrictedTestLift p q j s b w u v hu hv).appTop z)
    a.property
  change (restrictedTestLift p q j s b w u v hu hv ≫ testFirst F s b).appTop a.val =
    (restrictedTestLift p q j s b w u v hu hv ≫ testSecond F H s hs b).appTop a.val at h
  rw [restrictedTestLift_first, restrictedTestLift_second p q j s hs b w u v hu hv hb] at h
  exact h

end FLT.Mazur.SchemeScalarRelationPullback
