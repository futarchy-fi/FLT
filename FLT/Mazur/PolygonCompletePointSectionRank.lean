/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionFree
public import FLT.Mazur.FieldBaseSectionDimension

/-!
# Exact ranks of integral point-power sections

Canonical base change to the original closed polygon computes the rank of
complete-base sections. In particular every positive pole bound has a basis
of exactly that size over the original complete coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback IncreasingCechCoefficients Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual complete-base positive point-power section module has the expected rank. -/
theorem completePointPower_sections_finrank (i : Fin n) (m : ℕ) :
    Module.finrank Γ(Spec (.of (PowerSeries K)), ⊤)
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) = m + 1 := by
  let _ := completePointPower_sections_free K n h i m
  let _ : Algebra Γ(Spec (.of (PowerSeries K)), ⊤) Γ(Spec (.of K), ⊤) :=
    (completeClosedBase K).appTop.hom.toAlgebra
  let e := completePointPowerSectionsEquiv K n h (completeClosedBase K)
    (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiber_isPullback K n h) i m
  rw [← Module.finrank_baseChange (R := Γ(Spec (.of K), ⊤)), e.finrank_eq,
    baseSections_finrank_eq_scalarH0]
  exact completePointPower_closed_h0 K n h i (m + 1) (by omega)

/-- A finite integral basis of the actual section module, with the proved pole-bound size. -/
def completePointPowerSectionsBasis (i : Fin n) (m : ℕ) :
    Module.Basis (Fin (m + 1)) Γ(Spec (.of (PowerSeries K)), ⊤)
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) := by
  let _ := completePointPower_sections_finite K n h i m
  let _ := completePointPower_sections_free K n h i m
  exact Module.finBasisOfFinrankEq _ _ (completePointPower_sections_finrank K n h i m)

end FLT.Mazur.PolygonInfinitesimalStages
