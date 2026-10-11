/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageCoefficientBoundary
public import FLT.Mazur.PolygonCompatibleSectionScalars

/-!
# Complete-base scalars under the original coefficient pullback

The degree-zero formula and the actual structural square identify the
power-series coefficient action, including the original smoothing parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryLine family
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
  (m n : ℕ) (h : 2 ≤ n)

/-- The entire original family square retains the actual complete-base coefficient map. -/
@[reassoc] theorem stageCoefficientFamily_toSeries :
    stageCoefficientFamily f m n h ≫ (family R m n h).hom ≫ baseToSeries R m =
      (family S m n h).hom ≫ baseToSeries S m ≫
        Spec.map (CommRingCat.ofHom (PowerSeries.map f)) := by
  rw [← Category.assoc, (stageCoefficientFamily_isPullback f m n h).w,
    Category.assoc, stageCoefficientBase_toSeries]

/-- Coefficient pullback on boundary sections is semilinear over the original series map. -/
theorem coefficientBoundarySections_series (r : PowerSeries R) :
    coefficientBoundarySections f m n h (boundarySeriesScalars R n h m r) =
      boundarySeriesScalars S n h m (PowerSeries.map f r) := by
  rw [boundarySeriesScalars_eq, coefficientBoundarySections_of,
    SectionGradedLinePullback.sectionMap_zero, boundarySeriesScalars_eq]
  congr 1
  have he := congrArg
    (fun k : (family S m n h).left ⟶ Spec (.of (PowerSeries R)) ↦
      k.appTop ((Scheme.ΓSpecIso (.of (PowerSeries R))).inv r))
    (stageCoefficientFamily_toSeries f m n h)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at he
  refine he.trans ?_
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (PowerSeries.map f))) r
  exact congrArg ((family S m n h).hom.appTop ∘ (baseToSeries S m).appTop) hn.symm

/-- The chosen smoothing parameter is unchanged by coefficient pullback. -/
theorem coefficientBoundarySections_parameter :
    coefficientBoundarySections f m n h (boundarySeriesScalars R n h m PowerSeries.X) =
      boundarySeriesScalars S n h m PowerSeries.X := by
  rw [coefficientBoundarySections_series, PowerSeries.map_X]

end FLT.Mazur.PolygonInfinitesimalStages
