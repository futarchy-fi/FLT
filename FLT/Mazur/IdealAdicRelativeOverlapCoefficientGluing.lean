/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapMapCompatibility
public import FLT.Mazur.IdealAdicRelativeOverlapSpectrumMaps

/-!
# Coefficient comparisons on full relative overlaps

The original affine coefficient comparisons glue to isomorphisms on the
entire overlaps. Pulling back recovers each original affine comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOpenImmersionGluing

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U V : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart relativeTensorChart
attribute [local irreducible] relativeChartCoefficientSheaf relativeCoefficientAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The concrete spectrum coefficient maps satisfy the full gluing condition. -/
lemma relativeOverlapSpectrumChartMaps_compatible :
    Compatible (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1} ↦
        Spec (.of (RelativeAlgebra J f W.val)))
      (fun W ↦ relativeTensorOverlapChart J f
        (homOfLE W.property.1) (homOfLE W.property.2))
      (fun W ↦ relativeOverlapSpectrumChartMap J f
        (homOfLE W.property.1) (homOfLE W.property.2)) := by
  exact relativeOverlapMaps_compatible J f U V _ _
    (fun _ i j ↦ relativeOverlapSpectrumChartMap J f i j)
    (fun _ _ i j k ↦ relativeOverlapSpectrumChartMap_refine J f i j k)

/-- The global coefficient comparison on the full overlap of two relative charts. -/
def relativeOverlapCoefficientIso :
    (pullback (relativeOverlapFirstProjection J f U V)).obj
        (relativeChartCoefficientSheaf J f U) ≅
      (pullback (relativeOverlapSecondProjection J f U V)).obj
        (relativeChartCoefficientSheaf J f V) :=
  glueIso (fun W : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1} ↦
      Spec (.of (RelativeAlgebra J f W.val)))
    (fun W ↦ relativeTensorOverlapChart J f
      (homOfLE W.property.1) (homOfLE W.property.2))
    (fun x ↦ by
      obtain ⟨W, i, j, hx⟩ := relativeTensorOverlapChart_jointly_surjective J f U V x
      exact ⟨⟨W, leOfHom i, leOfHom j⟩, hx⟩)
    (fun W ↦ relativeOverlapSpectrumChartMap J f
      (homOfLE W.property.1) (homOfLE W.property.2))
    (relativeOverlapSpectrumChartMaps_compatible J f U V) (fun _ ↦ inferInstance)

/-- The full-overlap isomorphism recovers every supplied spectrum comparison. -/
lemma relativeOverlapCoefficientIso_pullback {W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).map
        (relativeOverlapCoefficientIso J f U V).hom =
      relativeOverlapSpectrumChartMap J f i j := by
  unfold relativeOverlapCoefficientIso glueIso
  exact pullback_glue
    (fun T : {T : X.affineOpens // T.1 ≤ U.1 ∧ T.1 ≤ V.1} ↦
      Spec (.of (RelativeAlgebra J f T.val)))
    (fun T ↦ relativeTensorOverlapChart J f
      (homOfLE T.property.1) (homOfLE T.property.2))
    (fun x ↦ by
      obtain ⟨Z, k, l, hx⟩ := relativeTensorOverlapChart_jointly_surjective J f U V x
      exact ⟨⟨Z, leOfHom k, leOfHom l⟩, hx⟩)
    (fun T ↦ relativeOverlapSpectrumChartMap J f
      (homOfLE T.property.1) (homOfLE T.property.2))
    (relativeOverlapSpectrumChartMaps_compatible J f U V)
    (⟨W, leOfHom i, leOfHom j⟩ : {W : X.affineOpens // W.1 ≤ U.1 ∧ W.1 ≤ V.1})

/-- Pulling back the full-overlap comparison also recovers the original coefficient map. -/
lemma relativeOverlapCoefficientIso_pullback_original {W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).map
        (relativeOverlapCoefficientIso J f U V).hom =
      relativeOverlapCoefficientChartMap J f i j :=
  (relativeOverlapCoefficientIso_pullback J f U V i j).trans
    (relativeOverlapSpectrumChartMap_eq_original J f i j)

end FLT.Mazur.IdealAdicGradedPullback
