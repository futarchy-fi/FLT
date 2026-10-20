/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarRestrictedTests
public import FLT.Mazur.SchemeScalarSourceComparison
public import FLT.Mazur.SchemeFppfBoundaryCorrections

/-!
# Descent from a covering scalar chart to the whole original source

Full restricted relation equations suffice for effective descent once the
chart covers the original scalar-test source. Coverage concerns original
source points, not just their scalar values.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarRelationPullback
open SchemeFppfRelationDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeRelationRestriction.doubleDomain
  SchemeRelationRestriction.fst SchemeRelationRestriction.snd
  testFirst testSecond sourceComparison
variable {D X U S Y : Scheme.{0}} (p q : D ⟶ X) (j : U ⟶ X) (s : X ⟶ S)
  (hs : p ≫ s = q ≫ s) (b : Y ⟶ S)
local notation "F" => SchemeRelationRestriction.fst p q j
local notation "H" => SchemeRelationRestriction.snd p q j

include hs

/-- The original scalar equality holds on the full two-endpoint chart restriction. -/
theorem restricted_scalar_square : F ≫ j ≫ s = H ≫ j ≫ s := by
  rw [← SchemeRelationRestriction.arrow_fst_assoc,
    ← SchemeRelationRestriction.arrow_snd_assoc, hs]

local notation "hj" => restricted_scalar_square p q j s hs
local notation "cmp" => sourceComparison j s b
local notation "pt" => testFirst p s b
local notation "qt" => testSecond p q s hs b

variable [Etale j]
  (hc : ∀ x : testSource s b, pullback.fst s b x ∈ Set.range j)

/-- The chosen scalar chart is an actual singleton fppf cover under the image condition. -/
abbrev sourceComparisonCover : (testSource s b).Cover Scheme.fppfPrecoverage :=
  .singleton cmp (sourceComparison_covers j s b hc)

include hs

/-- Full restricted invariance gives every mixed equation on this actual covering chart. -/
theorem sourceComparison_compatible (a : testInvariants F H (j ≫ s) hj b) :
    Compatible pt qt (sourceComparisonCover j s b hc) (fun _ ↦ a.val) := by
  intro T i l u v w hu hv
  change w ≫ pt = u ≫ cmp at hu
  change w ≫ qt = v ≫ cmp at hv
  apply restricted_invariant_test p q j (j ≫ s) hj b a
    (w ≫ pullback.fst (p ≫ s) b) u v
  · have h := congrArg (fun z ↦ z ≫ pullback.fst s b) hu
    simpa only [Category.assoc, testFirst_fst, sourceComparison_fst] using h
  · have h := congrArg (fun z ↦ z ≫ pullback.fst s b) hv
    simpa only [Category.assoc, testSecond_fst, sourceComparison_fst] using h
  · have h₁ := congrArg (fun z ↦ z ≫ pullback.snd s b) hu
    have h₂ := congrArg (fun z ↦ z ≫ pullback.snd s b) hv
    simp only [Category.assoc, testFirst, testSecond, pullback.lift_snd,
      sourceComparison_snd] at h₁ h₂
    exact h₁.symm.trans h₂

variable (r : X ⟶ D) (hrp : r ≫ p = 𝟙 X) (hrq : r ≫ q = 𝟙 X)

include hc r hrp hrq

/-- The chart coefficient descends uniquely to the entire original scalar-test equalizer. -/
theorem sourceComparison_existsUnique (a : testInvariants F H (j ≫ s) hj b) :
    ∃! v : testInvariants p q s hs b, (cmp).appTop v.val = a.val := by
  obtain ⟨v, hv, huniq⟩ := compatible_existsUnique pt qt (sourceComparisonCover j s b hc)
    (testReflexivity p s b r hrp) (testReflexivity_first p s b r hrp)
    (testReflexivity_second p q s hs b r hrp hrq) (fun _ ↦ a.val)
    (sourceComparison_compatible p q j s hs b hc a)
  refine ⟨v, congrFun hv PUnit.unit, fun z hz ↦ huniq z ?_⟩
  exact funext (fun _ ↦ hz)

/-- Exact boundary values descend together with the coefficient to the full original test. -/
theorem sourceComparison_boundary_lift {Z : Scheme.{0}} (i : Z ⟶ testSource s b)
    (a : testInvariants F H (j ≫ s) hj b) (t : Γ(Z, ⊤))
    (ht : (pullback.snd i cmp).appTop a.val = (pullback.fst i cmp).appTop t) :
    ∃ v : testInvariants p q s hs b,
      i.appTop v.val = t ∧ (cmp).appTop v.val = a.val := by
  obtain ⟨v, hv, _⟩ := sourceComparison_existsUnique p q j s hs b hc r hrp hrq a
  refine ⟨v, ?_, hv⟩
  apply boundary_of_restriction pt qt (sourceComparisonCover j s b hc) i v t
  intro z
  change (pullback.snd i cmp).appTop ((cmp).appTop v.val) = _
  rw [hv]
  exact ht

end FLT.Mazur.SchemeScalarRelationPullback
