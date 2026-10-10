/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalStageProper
public import FLT.Mazur.PolygonInfinitesimalFieldFiber
public import FLT.Mazur.PolygonClassifiedFamily

/-!
# Classified genus-one families at every infinitesimal smoothing order

Every geometric fiber is the actual original cyclic polygon. Its specified
pinching presentation supplies the nodal core, constant global sections, and
computed genus one. Together with properness and flatness this proves the
existing classified genus-one family contract for each concrete stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.CurveFiberHypotheses FCurve.DRFiberClassification

variable (K : Type) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- Every geometric fiber of the finite-order stage has the original polygon classification. -/
theorem stage_classified : ClassifiedGeometricFibers (family K m n h).hom := by
  let _ : NeZero n := ⟨by omega⟩
  refine ⟨fun L _ _ s Y p q hp ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := PolygonInfinitesimal.fieldFiber_exists_cocone
    (Ring K m) (parameter K m) L n h s p q hp
  exact ⟨PolygonNodalCore.nodalFiberCore L n (by omega) a b hab,
    Or.inr ⟨n, by omega, a, b, hab⟩⟩

/-- The actual cohomology computation of every geometric polygon fiber gives genus one. -/
theorem stage_geometricGenus : NodalGenusOneGeometricFibers (family K m n h).hom := by
  let _ : NeZero n := ⟨by omega⟩
  refine ⟨fun L _ _ s Y p q hp ↦ ?_⟩
  let _ : IsProper q := MorphismProperty.of_isPullback hp
    (inferInstance : IsProper (family K m n h).hom)
  obtain ⟨a, b, hab⟩ := PolygonInfinitesimal.fieldFiber_exists_cocone
    (Ring K m) (parameter K m) L n h s p q hp
  let _ : IsProper (Over.mk q).hom := inferInstanceAs (IsProper q)
  exact PolygonGeometricGenus.fiberCore L n (by omega) a b hab

/-- Each concrete finite-order smoothing is a proper flat classified genus-one family. -/
theorem stage_classifiedGenusOne : ClassifiedGenusOneFamily (family K m n h).hom :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    stage_classified K m n h, stage_geometricGenus K m n h⟩

end FLT.Mazur.PolygonInfinitesimalStages
