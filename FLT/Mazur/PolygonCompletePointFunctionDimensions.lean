/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementLinear
public import FLT.Mazur.PolygonCompletePointPoleFunctions

/-!
# Dimensions and exact orders of the original pole functions

The actual complement filtration retains h0=m over the specified field.
The previously chosen new functions lie strictly outside the preceding
piece, so the original pole-two and pole-three functions have exact orders.
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

/-- The original positive pole-function space has dimension exactly its pole bound. -/
theorem completeCartesianPointFunctions_finrank (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Module.finrank L (divisorPoleSubmodule q
      (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m) = m := by
  rw [divisorPoleSubmodule_finrank]
  exact completeCartesianPointPower_h0 K n h L s p q hs i m hm

/-- The previously chosen new function has exact pole order on the original complement. -/
theorem completeCartesianPointNewFunction_not_mem (i : Fin n) (m : ℕ) (hm : 0 < m) :
    completeCartesianPointNewFunction K n h L s p q hs i m hm ∉
      divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m := by
  let x := (moduleScalarH0Equiv q _).symm
    (completeCartesianPointNewSection K n h L s p q hs i m hm)
  have hx := (divisorPowerH0Function_mem_lower_iff
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 q m x).not.mpr
      (completeCartesianPointNewSection_not_mem_range K n h L s p q hs i m hm)
  change divisorComplementFunction _ (m + 1)
    ((moduleScalarH0Equiv q _) ((moduleScalarH0Equiv q _).symm
      (completeCartesianPointNewSection K n h L s p q hs i m hm))) ∉ _ at hx
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx

/-- In particular, each new pole function is nonzero as an actual regular function. -/
theorem completeCartesianPointNewFunction_ne_zero (i : Fin n) (m : ℕ) (hm : 0 < m) :
    completeCartesianPointNewFunction K n h L s p q hs i m hm ≠ 0 := by
  intro hz
  apply completeCartesianPointNewFunction_not_mem K n h L s p q hs i m hm
  rw [hz]
  exact (divisorPoleFunctions _ m).zero_mem

/-- Every positive step of the original function filtration is strict. -/
theorem completeCartesianPointFunctions_lt_succ (i : Fin n) (m : ℕ) (hm : 0 < m) :
    divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m <
      divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1
        (m + 1) := by
  apply lt_of_le_of_ne (divisorPoleFunctions_le_succ _ m)
  intro he
  apply completeCartesianPointNewFunction_not_mem K n h L s p q hs i m hm
  rw [he]
  exact completeCartesianPointNewFunction_mem K n h L s p q hs i m hm

end FLT.Mazur.PolygonInfinitesimalStages
