/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleSectionRing
public import FLT.Mazur.PolygonPowerSeriesSystem

/-!
# Complete-base scalars on compatible polygon sections

The power-series action comes from the actual structure morphisms of every
stage. Compatibility is proved on those morphisms, with no lifting assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- Power-series scalars in each actual stage section ring, placed in degree zero. -/
def boundarySeriesScalars (m : ℕ) : PowerSeries R →+* boundaryGradedSections R n h m :=
  (algebraMap Γ((family R m n h).left, ⊤) (boundaryGradedSections R n h m)).comp
    (((family R m n h).hom ≫ baseToSeries R m).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (PowerSeries R))).inv.hom)

/-- Complete-base scalars have the specified degree-zero section in every stage. -/
theorem boundarySeriesScalars_eq (m : ℕ) (r : PowerSeries R) :
    boundarySeriesScalars R n h m r =
      of (boundaryLine R m n h) ⊤ 0
        (((family R m n h).hom ≫ baseToSeries R m).appTop
          ((Scheme.ΓSpecIso (.of (PowerSeries R))).inv r)) := rfl

/-- All actual stage transitions preserve the complete-base scalars. -/
theorem boundarySectionsMap_series {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap R n h f).comp (boundarySeriesScalars R n h b) =
      boundarySeriesScalars R n h a := by
  apply RingHom.ext
  intro r
  change boundarySectionsMap R n h f (boundarySeriesScalars R n h b r) = _
  rw [boundarySeriesScalars_eq, boundarySectionsMap_of, SectionGradedIso.pieceMap_zero,
    SectionGradedPullback.pull_zero, boundarySeriesScalars_eq]
  congr 1
  have hh := congrArg (fun k : (family R a n h).left ⟶ Spec (.of (PowerSeries R)) ↦
    k.appTop ((Scheme.ΓSpecIso (.of (PowerSeries R))).inv r)) (stageSystem_toSeries R n h f)
  rw [Scheme.Hom.comp_appTop] at hh
  exact hh

/-- The power-series coefficient ring acts on the compatible-section ring. -/
def compatibleSeriesScalars : PowerSeries R →+* compatibleSectionRing R n h :=
  compatibleSectionLift R n h (boundarySeriesScalars R n h)
    (fun f ↦ boundarySectionsMap_series R n h f)

/-- The compatible ring is an algebra over the actual complete coefficient base. -/
instance compatibleSectionAlgebra : Algebra (PowerSeries R) (compatibleSectionRing R n h) :=
  (compatibleSeriesScalars R n h).toAlgebra

/-- The complete-base algebra map evaluates to the original stage structure map. -/
theorem compatibleSectionEval_algebraMap (m : ℕ) (r : PowerSeries R) :
    compatibleSectionEval R n h m (algebraMap (PowerSeries R) (compatibleSectionRing R n h) r) =
      boundarySeriesScalars R n h m r := rfl

end FLT.Mazur.PolygonInfinitesimalStages
