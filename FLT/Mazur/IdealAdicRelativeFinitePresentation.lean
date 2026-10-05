/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeNoetherian
public import FLT.Mazur.IdealAdicRelativeClosedModule
public import FLT.Mazur.IdealAdicRelativeSheafFinite

/-!
# Finite presentation over the actual relative chart rings

Noetherianity supplies the missing relation finiteness for the original
coefficient modules. These statements concern sections on affine charts;
they do not identify a relative spectrum or assert a global presentation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U : X.affineOpens)

/-- The original total coefficient module is finitely presented over the relative tensor ring. -/
lemma relativeCoefficient_finitePresentation :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    let := (relativeMap J f U).toRingHom.toAlgebra
    Module.FinitePresentation (RelativeAlgebra J f U)
      (IdealAdicGradedSections.Sections (J.comap f) U.1) := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let := (relativeMap J f U).toRingHom.toAlgebra
  let _ := relativeAlgebra_isNoetherianRing J f U
  let _ : Module.Finite (RelativeAlgebra J f U)
      (IdealAdicGradedSections.Sections (J.comap f) U.1) :=
    relativeMap_finite J f U
  exact Module.finitePresentation_of_finite _ _

/-- The original relative quotient has finitely many relations as an ideal. -/
lemma relativeMap_kernel_fg :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    (RingHom.ker (relativeMap J f U).toRingHom).FG := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let _ := relativeAlgebra_isNoetherianRing J f U
  exact IsNoetherian.noetherian _

/-- The actual glued coefficient sections are finitely presented over the glued relative ring. -/
lemma relativeCoefficientModuleSheaf_finitePresentation :
    Module.FinitePresentation ((relativeScalarSheaf J f).obj.obj (.op U.1))
      ((relativeCoefficientModuleSheaf J f).val.obj (.op U.1)) := by
  let _ := relativeSheaf_isNoetherianRing J f U
  let _ := relativeCoefficientModuleSheaf_finite J f U
  exact Module.finitePresentation_of_finite _ _

/-- Relations of the original glued quotient are finitely generated on each affine chart. -/
lemma relativeSheafQuotient_kernel_fg :
    (RingHom.ker ((relativeSheafQuotient J f).hom.app (.op U.1)).hom).FG := by
  let _ : IsNoetherianRing ((relativeRingSheaf J f).obj.obj (.op U.1)) :=
    relativeSheaf_isNoetherianRing J f U
  exact IsNoetherian.noetherian _

end FLT.Mazur.IdealAdicGradedPullback

namespace FLT.Mazur.IdealAdicGradedClosedAction

open FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U : X.affineOpens)

/-- Finite presentation for the actual closed coefficient module with its original action. -/
lemma relativeModule_finitePresentation :
    let := closedBaseAlgebra J f U.1
    let := relativeModule J f U
    Module.FinitePresentation (RelativeAlgebra J f U) (Total (J.comap f) U.1) := by
  let := closedBaseAlgebra J f U.1
  let := relativeModule J f U
  let _ := relativeAlgebra_isNoetherianRing J f U
  let _ := relativeModule_finite J f U
  exact Module.finitePresentation_of_finite _ _

end FLT.Mazur.IdealAdicGradedClosedAction
