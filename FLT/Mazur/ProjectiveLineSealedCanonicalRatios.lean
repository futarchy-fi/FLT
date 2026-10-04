/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSealedPullbackRatio
public import FLT.Mazur.ProjectiveLineCanonicalRatios

/-!
# Sealed canonical ratios on the marked projective line

The existing coordinate computation is connected once to the sealed pullback
ratio. Polygon specialization can then use the coordinate formula without
unfolding the inverse section morphism.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineCanonicalRatios
open FCurve ProjectiveLineMarkedHZero ProjectiveLineMarkedSectionTransition
open ProjectiveLineMarkedCharts
variable (K : Type u) [Field K] (a : Kˣ)

/-- The actual sealed pullback ratio has the marked polynomial formula. -/
lemma sealed_canonical_ratio (m : ℕ) (s : Γ(line K a m, ⊤)) :
    let := toLine_canonical_isIso K a m
    pullbackSectionRatio (toLine K a) (line K a m)
      (divisorSection ((relativeCartier K a).1.pow m) ⊤) s =
      coordinates K a (algebraMap K[X] (ring K a) (sectionPolynomial K a m s) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a : K)) ^ m) := by
  dsimp only
  rw [pullbackSectionRatio_def]
  exact toLine_canonical_ratio K a m s

end FLT.Mazur.ProjectiveLineCanonicalRatios
