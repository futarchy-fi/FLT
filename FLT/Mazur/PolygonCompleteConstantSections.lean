/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGeometricallyConnected
public import FLT.Mazur.ProperConnectedReducedSections
public import FLT.Mazur.CurveGenus

/-!
# Actual constant functions on all complete polygon field fibers

Connectedness, reducedness, properness and the retained original marking
identify actual global functions with the coefficient field. The induced
comparison computes actual degree-zero cohomology, including on geometric
generic fibers, without using completed cohomology in its place.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))

/-- Every actual field fiber has exactly its base-field constants as global functions. -/
theorem completeFieldFiber_constantSections :
    HasConstantGlobalSections (pullback.snd (exactVeroneseProjToBase K n h) s) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := exactVeroneseProjToBase_geometricallyReduced K n h
  let _ := exactVeroneseProjToBase_flat K n h
  let _ := completeFieldFiber_connected K n h L s
  exact constantGlobalSections_of_proper_connected_reduced_section (pullback.snd _ _)
    (completeFiberMarking K n h s ⟨0, by omega⟩) (completeFiberMarking_snd K n h s _)

/-- The original constants map is an equivalence onto actual degree-zero cohomology. -/
def completeFieldFiberH0Equiv :
    L ≃ₗ[L] H0 (pullback.snd (exactVeroneseProjToBase K n h) s) :=
  scalarH0ConstantsEquiv _ (completeFieldFiber_constantSections K n h L s)

/-- The actual comparison retains the original scalar map into cohomology. -/
theorem completeFieldFiberH0Equiv_apply (a : L) :
    completeFieldFiberH0Equiv K n h L s a =
      scalarH0Constants (pullback.snd (exactVeroneseProjToBase K n h) s) a := rfl

/-- Actual degree-zero cohomology of every field fiber is one-dimensional. -/
theorem completeFieldFiber_finrank_H0 :
    Module.finrank L (H0 (pullback.snd (exactVeroneseProjToBase K n h) s)) = 1 :=
  finrank_H0_of_constantGlobalSections _ (completeFieldFiber_constantSections K n h L s)

end FLT.Mazur.PolygonInfinitesimalStages
