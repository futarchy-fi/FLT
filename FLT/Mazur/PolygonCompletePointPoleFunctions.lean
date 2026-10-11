/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointLeadingClasses
public import FLT.Mazur.DivisorPowerComplementTransition

/-!
# Functions from the original pole-two and pole-three sections

The chosen new global sections give regular functions on the complement of
the original marked point. Their monomials have the expected pole bounds.
Exact pole order of products and a cubic presentation are separate steps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The original point complement, retaining its label on the specified field square. -/
def completeCartesianPointComplement (i : Fin n) : Y.Opens :=
  (completeCartesianMarking K n h s p q hs i).ker.support.compl

/-- A new actual pole section defines a regular function on the retained complement. -/
def completeCartesianPointNewFunction (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤) :=
  divisorComplementFunction (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    (m + 1) (completeCartesianPointNewSection K n h L s p q hs i m hm)

/-- The new function is represented in the original pole filtration by its chosen section. -/
theorem completeCartesianPointNewFunction_mem (i : Fin n) (m : ℕ) (hm : 0 < m) :
    completeCartesianPointNewFunction K n h L s p q hs i m hm ∈
      divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1
        (m + 1) :=
  ⟨completeCartesianPointNewSection K n h L s p q hs i m hm, rfl⟩

/-- Monomials in the actual pole-two and pole-three functions have bound 2a+3b. -/
theorem completeCartesianPoint_monomial_mem (i : Fin n) (a b : ℕ) :
    (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)) ^ a *
      (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) ^ b ∈
        divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1
          (2 * a + 3 * b) :=
  divisorPoleFunctions_mul _
    (divisorPoleFunctions_pow _
      (completeCartesianPointNewFunction_mem K n h L s p q hs i 1 (by decide)) a)
    (divisorPoleFunctions_pow _
      (completeCartesianPointNewFunction_mem K n h L s p q hs i 2 (by decide)) b)

/-- Every monomial of weighted degree at most six lies in the original sixth pole space. -/
theorem completeCartesianPoint_monomial_mem_six (i : Fin n) (a b : ℕ)
    (hab : 2 * a + 3 * b ≤ 6) :
    (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)) ^ a *
      (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) ^ b ∈
        divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1 6 :=
  divisorPoleFunctions_mono _ hab (completeCartesianPoint_monomial_mem
    K n h L s p q hs i a b)

end FLT.Mazur.PolygonInfinitesimalStages
