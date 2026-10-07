/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeLocalization
public import FLT.Mazur.IdealAdicRelativeChartScalar

/-!
# Principal charts inside the original relative tensor cover

The actual principal transition has the basic open of the actual chart scalar
as its range. Its image in the changed-base scheme is the original refined chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual principal chart transition has precisely the corresponding tensor basic open. -/
lemma relativeTensorTransition_basicOpen_range (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    let _ := relativeTensorTransition_isOpenImmersion J f i
    (relativeTensorTransition J f i).opensRange =
      PrimeSpectrum.basicOpen (relativeChartScalar J f V r) := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  let := (relativeRestriction J f i).toAlgebra
  let _ := relativeTensorTransition_isOpenImmersion J f i
  let _ : IsLocalization.Away (relativeChartScalar J f V r) (RelativeAlgebra J f U) := by
    simpa only [relativeChartScalar_apply] using
      relativeRestriction_basicOpen_isLocalization J f V r
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range (RelativeAlgebra J f U)
    (relativeChartScalar J f V r)

/-- The principal basic open maps to the original refined chart in the changed-base scheme. -/
lemma relativeTensorChart_basicOpen_image (V : X.affineOpens) (r : Γ(X, V.1)) :
    let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    let _ := relativeTensorChart_isOpenImmersion J f V
    let _ := relativeTensorChart_isOpenImmersion J f U
    relativeTensorChart J f V ''ᵁ PrimeSpectrum.basicOpen (relativeChartScalar J f V r) =
      (relativeTensorChart J f U).opensRange := by
  let U : X.affineOpens := ⟨X.basicOpen r, V.2.basicOpen r⟩
  let i : U.1 ⟶ V.1 := homOfLE (X.basicOpen_le r)
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  let _ := relativeTensorChart_isOpenImmersion J f V
  let _ := relativeTensorChart_isOpenImmersion J f U
  dsimp only
  rw [← relativeTensorTransition_basicOpen_range J f V r, ← Scheme.Hom.opensRange_comp]
  apply TopologicalSpace.Opens.ext
  change Set.range (relativeTensorTransition J f i ≫ relativeTensorChart J f V) =
    Set.range (relativeTensorChart J f U)
  rw [relativeTensorTransition_chart]

end FLT.Mazur.IdealAdicGradedPullback
