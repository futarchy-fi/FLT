/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianPointCohomology
public import FLT.Mazur.DivisorPowerH1Vanishing

/-!
# Reduction of the original point-power dimensions to the first power

On every original field square, a one-dimensional H0 for O(P) eliminates its
remaining H1. The actual divisor transitions then give h0(O(mP)) = m for all
positive m. The degree-one calculation is an explicit hypothesis here; it is
not supplied by the Euler formula or hidden in a presentation structure.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The missing first-power dimension is exactly what is needed to eliminate its H1. -/
theorem completeCartesianPointLine_first_h1_of_h0 (i : Fin n)
    (hfirst : Module.finrank L
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) 1) 0) = 1) :
    Subsingleton
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) 1) 1) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let M := tensorPower (completeCartesianPointLine K n h s p q hs i) 1
  let _ : M.IsFinitePresentation :=
    ((completeCartesianPointLine_rankOne K n h s p q hs i).tensorPower 1).isFinitePresentation
  let _ := proper_coherent_hasFiniteCohomology q M 1
  apply (Module.finrank_zero_iff (R := L)).mp
  have he := completeCartesianPointLine_power_h0_eq K n h L s p q hs i 1
  omega

/-- Solving degree one gives H1 vanishing for all original positive point powers. -/
theorem completeCartesianPointLine_positive_h1_of_first (i : Fin n)
    (hfirst : Module.finrank L
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) 1) 0) = 1)
    (m : ℕ) :
    Subsingleton
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1)) 1) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ := completeCartesianPoint_isFinite K n h L s p q hs i
  exact divisorPower_h1_subsingleton_of_first q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    (completeCartesianPointLine_first_h1_of_h0 K n h L s p q hs i hfirst) m

/-- Solving degree one computes every positive section dimension of the original point line. -/
theorem completeCartesianPointLine_positive_h0_of_first (i : Fin n)
    (hfirst : Module.finrank L
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) 1) 0) = 1)
    (m : ℕ) :
    Module.finrank L
      (ModuleScalarH q (tensorPower (completeCartesianPointLine K n h s p q hs i) (m + 1)) 0) =
        m + 1 := by
  let _ := completeCartesianPointLine_positive_h1_of_first K n h L s p q hs i hfirst m
  rw [completeCartesianPointLine_power_h0_eq, Module.finrank_zero_of_subsingleton, add_zero]

end FLT.Mazur.PolygonInfinitesimalStages
