/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeSchemeCharts
public import FLT.Mazur.IdealAdicRelativeFinitePresentation
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# A tensor chart cover and coherent coefficient modules

The original relative tensor spectra cover the actual changed-base scheme.
On each chart, the original coefficient module defines a coherent sheaf,
whose global sections are identified by the canonical tilde unit.
The overlap descent of these coefficient sheaves is not asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Every point of the changed-base scheme lies in an original relative tensor chart. -/
lemma relativeTensorChart_jointly_surjective (x : relativeScheme J f) :
    ∃ (U : X.affineOpens),
      let := closedBaseAlgebra J f U.1
      ∃ z : Spec (.of (RelativeAlgebra J f U)), relativeTensorChart J f U z = x := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show (J.comap f).subschemeι (relativeSchemeToClosed J f x) ∈ (⊤ : X.Opens) from trivial)
  let V : X.affineOpens := ⟨U, hU⟩
  let := closedBaseAlgebra J f V.1
  have hz : relativeSchemeToClosed J f x ∈
      Set.range (closedAffineChart J f V).2.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    exact hxU
  obtain ⟨z, hz⟩ := hz
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (relativeTensorChart_isPullback J f V) x z hz.symm
  exact ⟨V, w, hw⟩

/-- An open cover of the actual scheme by the original relative tensor spectra. -/
def relativeTensorCover : (relativeScheme J f).OpenCover where
  I₀ := X.affineOpens
  X U := let := closedBaseAlgebra J f U.1; Spec (.of (RelativeAlgebra J f U))
  f U := relativeTensorChart J f U
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨relativeTensorChart_jointly_surjective J f,
      fun U ↦ relativeTensorChart_isOpenImmersion J f U⟩

variable [IsLocallyNoetherian X] [IsAffine Y] (U : X.affineOpens)

/-- The original total coefficient module, over the original relative tensor ring. -/
def relativeChartCoefficient :
    let := closedBaseAlgebra J f U.1
    ModuleCat (RelativeAlgebra J f U) := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let := (relativeMap J f U).toRingHom.toAlgebra
  exact ModuleCat.of (RelativeAlgebra J f U)
    (IdealAdicGradedSections.Sections (J.comap f) U.1)

/-- The actual coefficient module gives a sheaf on the corresponding tensor spectrum. -/
def relativeChartCoefficientSheaf :
    let := closedBaseAlgebra J f U.1
    (Spec (.of (RelativeAlgebra J f U))).Modules := by
  let := closedBaseAlgebra J f U.1
  exact tilde (relativeChartCoefficient J f U)

/-- These are coherent sheaves on the actual affine charts. -/
instance relativeChartCoefficientSheaf_isFinitePresentation :
    let := closedBaseAlgebra J f U.1
    (relativeChartCoefficientSheaf J f U).IsFinitePresentation := by
  let := closedBaseAlgebra J f U.1
  let _ : Module.FinitePresentation (RelativeAlgebra J f U) (relativeChartCoefficient J f U) :=
    relativeCoefficient_finitePresentation J f U
  exact affineTilde_isFinitePresentation (R := .of (RelativeAlgebra J f U))
    (relativeChartCoefficient J f U)

/-- The chart sheaf retains the original coefficient module through the canonical tilde unit. -/
def relativeChartCoefficientSectionsIso :
    let := closedBaseAlgebra J f U.1
    relativeChartCoefficient J f U ≅
      moduleSpecΓFunctor.obj (relativeChartCoefficientSheaf J f U) := by
  let := closedBaseAlgebra J f U.1
  exact (tilde.toTildeΓNatIso (R := .of (RelativeAlgebra J f U))).app
    (relativeChartCoefficient J f U)

end FLT.Mazur.IdealAdicGradedPullback
