/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClassifiedFibers
public import FLT.Mazur.PolygonCompleteCartesianMarkings
public import FLT.Mazur.PolygonCompleteFieldH1
public import FLT.Mazur.PolygonCompleteConstantSections
public import FLT.Mazur.ClassifiedGenusOneFamily

/-!
# The original complete polygon is a classified genus-one family

The existing actual field H1 computation, classified nodal cores and original
markings assemble the genus-one contract for the original structure map.
It remains valid after every scheme base change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.CurveFiberHypotheses

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every specified field square retains the actual constant-functions property. -/
theorem completeCartesianField_constantSections (L : Type) [Field L]
    (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
    {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (exactVeroneseProjToBase K n h) s) :
    HasConstantGlobalSections q := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  have hc := (completeCartesianField_classified K n h L s p q hs).toNodalFiberCore
  let _ := hc.connected
  let _ := hc.reduced
  exact constantGlobalSections_of_proper_connected_reduced_section q
    (completeCartesianMarking K n h s p q hs ⟨0, by omega⟩)
    (completeCartesianMarking_snd K n h s p q hs _)

/-- The original complete family has actual genus one on all geometric fiber squares. -/
theorem exactVeroneseProjToBase_genusOneGeometricFibers :
    let _ := exactVeroneseProjToBase_isProper K n h
    NodalGenusOneGeometricFibers (exactVeroneseProjToBase K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  constructor
  intro L _ _ s Y p q hs
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  refine ⟨(completeCartesianField_classified K n h L s p q hs).toNodalFiberCore,
    completeCartesianField_constantSections K n h L s p q hs, ?_⟩
  exact completeCartesianFieldH1_finrank K n h L s p q hs

/-- The original complete polygon family satisfies the full classified genus-one contract. -/
theorem exactVeroneseProjToBase_classifiedGenusOneFamily :
    ClassifiedGenusOneFamily (exactVeroneseProjToBase K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := exactVeroneseProjToBase_flat K n h
  let _ := exactVeroneseProjToBase_lfp K n h
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    exactVeroneseProjToBase_classifiedGeometricFibers K n h,
    exactVeroneseProjToBase_genusOneGeometricFibers K n h⟩

/-- Every scheme base change retains the full classified genus-one contract. -/
theorem completeBaseChange_classifiedGenusOneFamily {S : Scheme}
    (s : S ⟶ Spec (.of (PowerSeries K))) :
    ClassifiedGenusOneFamily (pullback.snd (exactVeroneseProjToBase K n h) s) :=
  (exactVeroneseProjToBase_classifiedGenusOneFamily K n h).baseChange s

end FLT.Mazur.PolygonInfinitesimalStages
