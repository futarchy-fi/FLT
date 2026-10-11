/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianIdentityQuasiFinite
public import FLT.Mazur.PolygonCompleteCoefficientAdicComparison
public import FLT.Mazur.PolygonCompleteLineIsoDetection
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of the actual complete coefficient comparison

The original zero-stage cartesian identity lies in the quasi-finite locus.
Properness over the local base makes that open the entire source; proper
quasi-finite morphisms are finite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual comparison is quasi-finite at every point of every original stage. -/
theorem completeCoefficientComparison_quasiFiniteAt (m : ℕ) (x : (family L m n h).left) :
    (completeCoefficientComparison f n h).QuasiFiniteAt
      (originalStageToCompatibleProj L n h m x) := by
  let _ := completeCoefficientComparison_isProper f n h
  exact CartesianIdentity.quasiFiniteAt _ _
    (completeCoefficientComparison_stage_isPullback f n h m) x

/-- The zero stage detects that the quasi-finite locus covers the entire complete model. -/
theorem completeCoefficientComparison_locallyQuasiFinite :
    LocallyQuasiFinite (completeCoefficientComparison f n h) := by
  let _ := completeCoefficientComparison_isProper f n h
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  apply completeOpen_eq_top_of_originalZero L n h
  apply top_unique
  intro x _
  exact completeCoefficientComparison_quasiFiniteAt f n h 0 x

/-- The constructed proper comparison to the actual coefficient pullback is finite. -/
theorem completeCoefficientComparison_isFinite :
    IsFinite (completeCoefficientComparison f n h) := by
  let _ := completeCoefficientComparison_isProper f n h
  let _ := completeCoefficientComparison_locallyQuasiFinite f n h
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end FLT.Mazur.PolygonInfinitesimalStages
