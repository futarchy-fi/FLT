/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantCoordinates
public import FLT.GroupScheme.LocalFiniteFlatExtension
public import FLT.GroupScheme.HopfPointFiberTorsor

/-!
# The fibre at one of the canonical constant cyclic quotient

Evaluation at one is constructed from the proved coordinates of the canonical
constant model. The fibre comparison is derived from the Hopf quotient map;
no multiplicative-kernel identification or Kummer parameter is assumed.
The canonical constant model used here is over `ZInvTwo`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace ThreeAdicPlan

variable (n : ℕ) [NeZero n]

/-- The integral point one of the actual constant cyclic model. -/
def constantCyclicOnePoint :
    (constantFiniteFlat (ZMod n)).toFF.CoordinateRing →ₐ[ZInvTwo] ZInvTwo :=
  (Pi.evalAlgHom ZInvTwo (fun _ : ZMod n ↦ ZInvTwo) 1).comp
    (constantCoordinateEquiv (ZMod n)).toAlgHom

/-- Evaluation really takes the value at one in the proved constant coordinates. -/
@[simp] theorem constantCyclicOnePoint_apply
    (a : (constantFiniteFlat (ZMod n)).toFF.CoordinateRing) :
    constantCyclicOnePoint n a = constantCoordinateEquiv (ZMod n) a 1 := rfl

variable {X : FF ZInvTwo ℚ}
  (q : ModelHom X (constantFiniteFlat (ZMod n)).toFF)

/-- The fibre at one, formed directly from the actual quotient morphism. -/
def ConstantCyclicOneFiber :=
  letI := q.toAlgHom.toRingHom.toAlgebra
  HopfAlgebra.PointFiber (A := X.CoordinateRing) (constantCyclicOnePoint n)

/-- The canonical comparison on the fibre at one of the constant quotient. -/
def constantCyclicOneFiberComparison :
    letI := q.toAlgHom.toRingHom.toAlgebra
    HopfAlgebra.PointFiber (A := X.CoordinateRing) (constantCyclicOnePoint n) ⊗[ZInvTwo]
      HopfAlgebra.PointFiber (A := X.CoordinateRing) (constantCyclicOnePoint n) ≃ₐ[
        HopfAlgebra.PointFiber (A := X.CoordinateRing) (constantCyclicOnePoint n)]
      HopfAlgebra.PointFiber (A := X.CoordinateRing) (constantCyclicOnePoint n) ⊗[ZInvTwo]
        (X.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal q) := by
  let : Algebra (constantFiniteFlat (ZMod n)).toFF.CoordinateRing X.CoordinateRing :=
    q.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower ZInvTwo (constantFiniteFlat (ZMod n)).toFF.CoordinateRing
      X.CoordinateRing := IsScalarTower.of_algebraMap_eq' q.toAlgHom.comp_algebraMap.symm
  exact HopfAlgebra.pointFiberTorsorEquiv q (by ext; rfl) (constantCyclicOnePoint n)

/-- In an actual extension the fibre at one is a finite faithfully flat cover. -/
theorem constantCyclicOneFiber_finite_faithfullyFlat {H : FF ZInvTwo ℚ}
    (E : ModelExtension H X (constantFiniteFlat (ZMod n)).toFF) :
    letI := E.quotient.toAlgHom.toRingHom.toAlgebra
    Module.Finite ZInvTwo
      (HopfAlgebra.PointFiber (A := X.CoordinateRing) (constantCyclicOnePoint n)) ∧
    Module.FaithfullyFlat ZInvTwo
      (HopfAlgebra.PointFiber (A := X.CoordinateRing) (constantCyclicOnePoint n)) := by
  let : Algebra (constantFiniteFlat (ZMod n)).toFF.CoordinateRing X.CoordinateRing :=
    E.quotient.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower ZInvTwo (constantFiniteFlat (ZMod n)).toFF.CoordinateRing
      X.CoordinateRing := IsScalarTower.of_algebraMap_eq' E.quotient.toAlgHom.comp_algebraMap.symm
  let : Module.FaithfullyFlat (constantFiniteFlat (ZMod n)).toFF.CoordinateRing
      X.CoordinateRing := E.quotientFaithfullyFlat
  exact ⟨inferInstance, inferInstance⟩

end ThreeAdicPlan
