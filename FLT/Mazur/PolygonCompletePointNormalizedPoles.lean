/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointWeierstrassEquation

/-!
# The normalized coordinates retain their exact poles

Normalization by the nonzero original cubic leading coefficient preserves
every original pole subspace. In particular the normalized Weierstrass
coordinates still have exact orders two and three at the retained marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Simultaneous coordinate normalization preserves every original pole bound. -/
theorem completeCartesianPointNormalize_mem_iff (i : Fin n) (m : ℕ)
    (z : Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)) :
    completeCartesianPointNormalize K n h L s p q hs i z ∈
      divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m ↔
    z ∈ divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m :=
  Submodule.smul_mem_iff
    (divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m)
    (completeCartesianPointCubicCoefficients_last_ne_zero K n h L s p q hs i)

/-- Normalized original new functions retain their upper pole bound. -/
theorem completeCartesianPointNormalizedFunction_mem (i : Fin n) (m : ℕ) (hm : 0 < m) :
    completeCartesianPointNormalize K n h L s p q hs i
      (completeCartesianPointNewFunction K n h L s p q hs i m hm) ∈
      divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1
        (m + 1) := by
  rw [completeCartesianPointNormalize_mem_iff, mem_divisorPoleSubmodule]
  exact completeCartesianPointNewFunction_mem K n h L s p q hs i m hm

/-- Their pole orders remain exact, including the normalized x and y coordinates. -/
theorem completeCartesianPointNormalizedFunction_not_mem (i : Fin n) (m : ℕ) (hm : 0 < m) :
    completeCartesianPointNormalize K n h L s p q hs i
      (completeCartesianPointNewFunction K n h L s p q hs i m hm) ∉
      divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m := by
  rw [completeCartesianPointNormalize_mem_iff, mem_divisorPoleSubmodule]
  exact completeCartesianPointNewFunction_not_mem K n h L s p q hs i m hm

end FLT.Mazur.PolygonInfinitesimalStages
