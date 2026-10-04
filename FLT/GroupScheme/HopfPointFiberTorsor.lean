/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsorSpecialization
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# The canonical torsor comparison on a point fibre

The fibre of a Hopf quotient over an integral point has the canonical comparison
with the augmentation kernel. This is constructed by base change, even when
the fibre has no point over the original ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open Algebra.TensorProduct
namespace HopfAlgebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]
  [Algebra B A] [IsScalarTower R B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R)

/-- The actual coordinate algebra of the fibre over the chosen point. -/
@[implicit_reducible]
def PointFiber := let := p.toRingHom.toAlgebra; R ⊗[B] A

instance : CommRing (PointFiber (A := A) p) := by unfold PointFiber; infer_instance
instance : Algebra R (PointFiber (A := A) p) := by unfold PointFiber; infer_instance
instance : Module R (PointFiber (A := A) p) := Algebra.toModule

/-- Pullback from the middle coordinate algebra to the point fibre. -/
def pointFiberMap : A →ₐ[R] PointFiber (A := A) p := by
  let : Algebra B R := p.toRingHom.toAlgebra
  let : IsScalarTower R B R := IsScalarTower.of_algebraMap_eq' p.comp_algebraMap.symm
  exact (includeRight : A →ₐ[B] R ⊗[B] A).restrictScalars R

/-- Faithfully flat quotient maps have faithfully flat point fibres. -/
instance pointFiber_faithfullyFlat [Module.FaithfullyFlat B A] :
    Module.FaithfullyFlat R (PointFiber (A := A) p) := by
  let : Algebra B R := p.toRingHom.toAlgebra
  change Module.FaithfullyFlat R (R ⊗[B] A)
  infer_instance

/-- A finite middle model has a finite fibre over each integral quotient point. -/
instance pointFiber_finite [Module.Finite R A] :
    Module.Finite R (PointFiber (A := A) p) := by
  let : Algebra B R := p.toRingHom.toAlgebra
  let : Module.Finite B A := Module.Finite.of_restrictScalars_finite R B A
  change Module.Finite R (R ⊗[B] A)
  infer_instance

/-- The fibre comparison is the pullback of the canonical Hopf comparison. -/
def pointFiberTorsorEquiv :
    PointFiber (A := A) p ⊗[R] PointFiber (A := A) p ≃ₐ[PointFiber (A := A) p]
      PointFiber (A := A) p ⊗[R] (A ⧸ augmentationIdeal f) := by
  let : Algebra B R := p.toRingHom.toAlgebra
  let : IsScalarTower R B R := IsScalarTower.of_algebraMap_eq' p.comp_algebraMap.symm
  let : Algebra A (R ⊗[B] A) := rightAlgebra
  let : IsScalarTower R A (R ⊗[B] A) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change r ⊗ₜ[B] (1 : A) = (1 : R) ⊗ₜ[B] algebraMap R A r
    have h := TensorProduct.tmul_smul (R := B) (algebraMap R B r) (1 : R) (1 : A)
    simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R B A,
      ← IsScalarTower.algebraMap_apply R B R] using h.symm
  change (R ⊗[B] A) ⊗[R] (R ⊗[B] A) ≃ₐ[R ⊗[B] A]
    (R ⊗[B] A) ⊗[R] (A ⧸ augmentationIdeal f)
  exact (cancelBaseChange B R (R ⊗[B] A) (R ⊗[B] A) A).trans
    (specializedTorsorEquiv f hf)

/-- The kernel coaction on the actual point fibre. -/
def pointFiberCoaction : PointFiber (A := A) p →ₐ[R]
    PointFiber (A := A) p ⊗[R] (A ⧸ augmentationIdeal f) :=
  ((pointFiberTorsorEquiv f hf p).restrictScalars R).toAlgHom.comp includeRight

/-- The coaction on a fibre is induced by the coaction on the middle model. -/
theorem pointFiberCoaction_map (a : A) :
    pointFiberCoaction f hf p (pointFiberMap (A := A) p a) =
      Algebra.TensorProduct.map (pointFiberMap (A := A) p)
        (AlgHom.id R (A ⧸ augmentationIdeal f)) (torsorCoaction f a) := by
  let : Algebra B R := p.toRingHom.toAlgebra
  let : IsScalarTower R B R := IsScalarTower.of_algebraMap_eq' p.comp_algebraMap.symm
  let : Algebra A (R ⊗[B] A) := rightAlgebra
  let : IsScalarTower R A (R ⊗[B] A) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change r ⊗ₜ[B] (1 : A) = (1 : R) ⊗ₜ[B] algebraMap R A r
    have h := TensorProduct.tmul_smul (R := B) (algebraMap R B r) (1 : R) (1 : A)
    simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R B A,
      ← IsScalarTower.algebraMap_apply R B R] using h.symm
  change specializedTorsorEquiv f hf
    (cancelBaseChange B R (R ⊗[B] A) (R ⊗[B] A) A
      (1 ⊗ₜ[R] (1 ⊗ₜ[B] a))) = _
  rw [cancelBaseChange_tmul, one_smul]
  exact specializedTorsorEquiv_second f hf a

end HopfAlgebra
