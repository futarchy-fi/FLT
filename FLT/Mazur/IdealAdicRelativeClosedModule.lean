/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicClosedGradedModule
public import FLT.Mazur.IdealAdicRelativeGradedAlgebra

/-!
# Finite relative modules of actual closed coefficients

The relative algebra acts on the direct sum of the actual closed coefficient
sections. The canonical comparison is linear, and this module is finite on
every ambient affine chart. This does not assert a global sheaf gluing theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedPullback FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedClosedAction

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U : X.affineOpens)

/-- The actual closed total coefficient is a module over the relative graded algebra. -/
@[instance_reducible]
def relativeModule :
    let := closedBaseAlgebra J f U.1
    Module (RelativeAlgebra J f U) (Total (J.comap f) U.1) := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let := (relativeMap J f U).toRingHom.toAlgebra
  exact (totalEquiv (J.comap f) U.1).module (RelativeAlgebra J f U)

/-- The closed pushforward comparison is linear over the actual relative algebra. -/
def relativeLinearEquiv :
    let := closedBaseAlgebra J f U.1
    let := localBaseAlgebra J f U.1
    let := (relativeMap J f U).toRingHom.toAlgebra
    let := relativeModule J f U
    Total (J.comap f) U.1 ≃ₗ[RelativeAlgebra J f U]
      IdealAdicGradedSections.Sections (J.comap f) U.1 := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let := (relativeMap J f U).toRingHom.toAlgebra
  exact (totalEquiv (J.comap f) U.1).linearEquiv (RelativeAlgebra J f U)

/-- Finiteness holds for the actual closed coefficient module over the relative algebra. -/
lemma relativeModule_finite :
    let := closedBaseAlgebra J f U.1
    let := relativeModule J f U
    Module.Finite (RelativeAlgebra J f U) (Total (J.comap f) U.1) := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let := (relativeMap J f U).toRingHom.toAlgebra
  let := relativeModule J f U
  let : Module.Finite (RelativeAlgebra J f U)
      (IdealAdicGradedSections.Sections (J.comap f) U.1) := relativeMap_finite J f U
  exact Module.Finite.equiv (relativeLinearEquiv J f U).symm

/-- The relative action retains multiplication by actual base and closed scalar sections. -/
lemma relativeModule_smul_tmul (a : IdealAdicGradedSections.Sections J ⊤)
    (r : ClosedScalars (J.comap f) U.1) (t : Total (J.comap f) U.1) :
    let := closedBaseAlgebra J f U.1
    let := relativeModule J f U
    totalEquiv (J.comap f) U.1 ((a ⊗ₜ[Γ(Y, ⊤)] r) • t) =
      localRingHom J f U.1 a * closedScalarAdd (J.comap f) U.1 r *
        totalEquiv (J.comap f) U.1 t := by
  let := closedBaseAlgebra J f U.1
  let := localBaseAlgebra J f U.1
  let := (relativeMap J f U).toRingHom.toAlgebra
  let := relativeModule J f U
  change totalEquiv (J.comap f) U.1 ((totalEquiv (J.comap f) U.1).symm
    (relativeMap J f U (a ⊗ₜ[Γ(Y, ⊤)] r) * totalEquiv (J.comap f) U.1 t)) = _
  rw [AddEquiv.apply_symm_apply, relativeMap_tmul]
  rfl

end FLT.Mazur.IdealAdicGradedClosedAction
