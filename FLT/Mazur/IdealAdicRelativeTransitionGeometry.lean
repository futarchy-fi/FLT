/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeChartTransition

/-!
# Cartesian geometry of the original relative transitions

Every transition is the base change of the actual closed chart restriction.
The maps form a functor on ambient affine opens and are open immersions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Transition maps are actual Cartesian base changes of closed chart restrictions. -/
lemma relativeTensorTransition_isPullback {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    IsPullback (relativeTensorTransition J f i) (relativeTensorToChart J f U)
      (relativeTensorToChart J f V)
      (Spec.map (CommRingCat.ofHom (closedScalarRestriction (J.comap f) i))) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  have h : IsPullback (relativeTensorTransition J f i ≫ relativeTensorChart J f V)
      (relativeTensorToChart J f U) (relativeSchemeToClosed J f)
      (Spec.map (CommRingCat.ofHom (closedScalarRestriction (J.comap f) i)) ≫
        (closedAffineChart J f V).2.fromSpec) := by
    rw [relativeTensorTransition_chart, closedAffineChart_restrict]
    exact relativeTensorChart_isPullback J f U
  exact h.of_right (relativeTensorTransition_toChart J f i)
    (relativeTensorChart_isPullback J f V)

/-- Relative transitions are open immersions between the original tensor spectra. -/
lemma relativeTensorTransition_isOpenImmersion {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f U.1
    IsOpenImmersion (relativeTensorTransition J f i) := by
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f U.1
  let _ := relativeTensorChart_isOpenImmersion J f V
  have h : IsOpenImmersion
      (relativeTensorTransition J f i ≫ relativeTensorChart J f V) := by
    rw [relativeTensorTransition_chart]
    exact relativeTensorChart_isOpenImmersion J f U
  exact IsOpenImmersion.of_comp (relativeTensorTransition J f i) (relativeTensorChart J f V)

/-- The original transition on an identity inclusion is the identity scheme map. -/
lemma relativeTensorTransition_id (U : X.affineOpens) :
    let := closedBaseAlgebra J f U.1
    relativeTensorTransition J f (𝟙 U.1) = 𝟙 _ := by
  let := closedBaseAlgebra J f U.1
  unfold relativeTensorTransition
  rw [relativeRestriction_id]
  exact Spec.map_id _

/-- The transition of a composite inclusion is the composite of the actual transitions. -/
lemma relativeTensorTransition_comp {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    relativeTensorTransition J f i ≫ relativeTensorTransition J f j =
      relativeTensorTransition J f (i ≫ j) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  unfold relativeTensorTransition
  rw [← Spec.map_comp]
  exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h.toRingHom))
    (relativeRestriction_comp J f i j)

/-- The original tensor spectra and restriction maps form the actual affine chart diagram. -/
def relativeTensorDiagram : X.affineOpens ⥤ Scheme.{u} where
  obj U := let := closedBaseAlgebra J f U.1; Spec (.of (RelativeAlgebra J f U))
  map i := relativeTensorTransition J f (homOfLE i.le)
  map_id U := relativeTensorTransition_id J f U
  map_comp i j := (relativeTensorTransition_comp J f (homOfLE i.le) (homOfLE j.le)).symm

/-- The chart diagram maps naturally into the changed-base scheme. -/
def relativeTensorDiagramToScheme :
    relativeTensorDiagram J f ⟶ (Functor.const X.affineOpens).obj (relativeScheme J f) where
  app U := relativeTensorChart J f U
  naturality U V i := by
    change relativeTensorTransition J f (homOfLE i.le) ≫ relativeTensorChart J f V =
      relativeTensorChart J f U ≫ 𝟙 _
    rw [Category.comp_id, relativeTensorTransition_chart]

end FLT.Mazur.IdealAdicGradedPullback
