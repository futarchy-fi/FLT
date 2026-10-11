/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.PolygonDivisorPowerPullback
public import FLT.Mazur.ProjectiveLineMarkedSectionTransition
public import FLT.Mazur.DivisorLineBundlePower
public import Mathlib.Tactic.IrreducibleDef

/-!
# Actual single-point powers on polygon normalization

All ideal powers retain their original multiplicities. On the marked
component they are the very same P1 line used by the bounded-polynomial
coordinates. On other components they remain the empty divisor line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonSinglePointLineNormalization

open FCurve PolygonPinching PolygonMarkedSections PolygonDivisorNormalizationPullback
open FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual divisor sheaf O(mP) for one original polygon marking. -/
def pointPower (a : Kˣ) (j : Fin n) (m : ℕ) : C.left.Modules :=
  divisorLineBundle ((sectionMap K n p a j).ker ^ m)
    ((section_cartier K n p hn q h a j).1.pow m)

/-- This ideal-power coefficient is the tensor power of the original single-point line. -/
def pointPowerIso (a : Kˣ) (j : Fin n) (m : ℕ) :
    tensorPower (pointLine K n hn p q h a j) m ≅ pointPower K n hn p q h a j m :=
  divisorLineBundlePowerIso (section_cartier K n p hn q h a j).1 m

include h in
/-- Every power has an invertible actual ideal comparison on every component. -/
theorem pointPowerIdealComparison_isIso (a : Kˣ) (i j : Fin n) (m : ℕ) :
    IsIso (idealModulePullbackHom ((sectionMap K n p a j).ker ^ m)
      (componentι K n i ≫ p).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _ ((section_cartier K n p hn q h a j).1.pow m)
  rw [idealSheaf_comap_pow]
  apply EffectiveCartier.pow
  by_cases hij : i = j
  · subst j
    rw [section_ideal K n hn p q h a i]
    exact (ProjectiveLineMarkedCharts.relativeCartier K a).1
  · rw [other_section_ideal K n hn p q h a hij]
    exact effectiveCartier_top

/-- On its marked component O(mP) is the original polynomial-coordinate line. -/
irreducible_def ownComponentPowerIso (a : Kˣ) (j : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback (componentι K n j ≫ p).left).obj
      (pointPower K n hn p q h a j m) ≅ ProjectiveLineMarkedSectionTransition.line K a m := by
  let _ := pointPowerIdealComparison_isIso K n hn p q h a j j m
  exact divisorLinePullbackIsoOfEq _ ((section_cartier K n p hn q h a j).1.pow m)
    ((ProjectiveLineMarkedCharts.relativeCartier K a).1.pow m)
    (by rw [idealSheaf_comap_pow, section_ideal K n hn p q h a j])

/-- On every other component the full ideal power is canonically trivial. -/
irreducible_def otherComponentPowerIso (a : Kˣ) {i j : Fin n} (hij : i ≠ j) (m : ℕ) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (pointPower K n hn p q h a j m) ≅ structureModule (ProjectiveLine.scheme K) := by
  let _ := pointPowerIdealComparison_isIso K n hn p q h a i j m
  exact divisorLinePullbackIsoOfEq _ ((section_cartier K n p hn q h a j).1.pow m)
    effectiveCartier_top (by
      rw [idealSheaf_comap_pow, other_section_ideal K n hn p q h a hij]
      simp only [← Scheme.IdealSheafData.one_eq_top, one_pow]) ≪≫
        divisorLineBundleTopIso effectiveCartier_top

end FLT.Mazur.PolygonSinglePointLineNormalization
