/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationLinearSections
public import FLT.Mazur.PolygonSinglePointPowerSections
public import FLT.Mazur.ProjectiveLinePointLoopMatching

/-!
# Linear coordinates for single-point normalization powers

For the original O(mP), the marked component contributes its actual projective-line
H0 and every other component contributes one scalar. These are coordinates for the
whole normalization H0, before imposing the node matching equations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.PolygonSinglePointHZeroCoordinates

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonNormalizationLinearSections

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Splitting one factor from a dependent product is linear. -/
def linearPiSplitAt {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (j : ι) :
    (∀ i, V i) ≃ₗ[K] V j × (∀ i : {i // i ≠ j}, V i.val) :=
  { toEquiv := Equiv.piSplitAt j V
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- The marked component H0 uses the original polynomial-coordinate line. -/
def ownEquiv :
    ModuleScalarH (component K).hom
        (componentLine K n p (pointPower K n hn p q h a j m) j) 0 ≃ₗ[K]
      ProjectiveLineMarkedHZero.H0 K a m :=
  ((moduleScalarHFunctor (component K).hom 0).mapIso
    (ownComponentPowerIso K n hn p q h a j m)).toLinearEquiv

/-- Every unmarked component H0 is canonically one copy of the base field. -/
def otherEquiv (i : {i : Fin n // i ≠ j}) :
    ModuleScalarH (component K).hom
        (componentLine K n p (pointPower K n hn p q h a j m) i.val) 0 ≃ₗ[K] K :=
  (((moduleScalarHFunctor (component K).hom 0).mapIso
    (otherComponentPowerIso K n hn p q h a i.property m)).toLinearEquiv.trans
      (moduleScalarHUnitEquiv (component K).hom 0)).trans
        (ProjectiveLineConstantSections.h0Equiv K)

/-- All normalization sections are one marked H0 class and independent unmarked scalars. -/
def coordinates : ModuleScalarH C.hom ((pushforward p.left).obj
    ((Scheme.Modules.pullback p.left).obj (pointPower K n hn p q h a j m))) 0 ≃ₗ[K]
      ProjectiveLineMarkedHZero.H0 K a m × ({i : Fin n // i ≠ j} → K) :=
  (componentEquiv K n p (pointPower K n hn p q h a j m)).trans
    ((linearPiSplitAt _ j).trans
      ((ownEquiv K n hn p q h a j m).prodCongr
        (LinearEquiv.piCongrRight (otherEquiv K n hn p q h a j m))))

/-- The first coordinate is the actual restriction to the marked component. -/
theorem coordinates_fst (x : ModuleScalarH C.hom ((pushforward p.left).obj
    ((Scheme.Modules.pullback p.left).obj (pointPower K n hn p q h a j m))) 0) :
    (coordinates K n hn p q h a j m x).1 =
      ownEquiv K n hn p q h a j m
        (componentEquiv K n p (pointPower K n hn p q h a j m) x j) := rfl

/-- Every remaining scalar comes from the canonical trivialization on that component. -/
theorem coordinates_snd (x : ModuleScalarH C.hom ((pushforward p.left).obj
    ((Scheme.Modules.pullback p.left).obj (pointPower K n hn p q h a j m))) 0)
    (i : {i : Fin n // i ≠ j}) :
    (coordinates K n hn p q h a j m x).2 i =
      otherEquiv K n hn p q h a j m i
        (componentEquiv K n p (pointPower K n hn p q h a j m) x i.val) := rfl

end FLT.Mazur.PolygonSinglePointHZeroCoordinates
