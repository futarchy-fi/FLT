/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwoGeneratorRelationSequence
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flat base change of the explicit relation kernel

The relation differential commutes with arbitrary scalar extension, and its
kernel commutes with flat scalar extension.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.TwoGeneratorRelation

open TensorProduct

variable {C : Type*} [CommRing C] (x y : C) (S : Type*) [CommRing S] [Algebra C S]

/-- The free pair after scalar extension, with its original ordered coordinates. -/
def pairBaseChangeEquiv : S ⊗[C] (C × C) ≃ₗ[S] S × S :=
  TensorProduct.prodRight C S S C C ≪≫ₗ
    (AlgebraTensorModule.rid C S S).prodCongr (AlgebraTensorModule.rid C S S)

/-- The relation differential commutes with the free-module base change identifications. -/
theorem relationMap_baseChange_comm :
    (pairBaseChangeEquiv (C := C) S).toLinearMap.comp ((relationMap x y).baseChange S) =
      (relationMap (algebraMap C S x) (algebraMap C S y)).comp
        (AlgebraTensorModule.rid C S S).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro a b
  simp [pairBaseChangeEquiv, relationMap_apply, Algebra.smul_def,
    mul_left_comm, mul_comm]

attribute [local irreducible] pairBaseChangeEquiv

/-- The scalar-extended differential has the same kernel as the new coefficient matrix. -/
def relationBaseChangeKernelEquiv : LinearMap.ker ((relationMap x y).baseChange S) ≃ₗ[S]
    LinearMap.ker (relationMap (algebraMap C S x) (algebraMap C S y)) :=
  LinearEquiv.ofEq _ _ (by
    rw [← LinearMap.ker_comp, ← relationMap_baseChange_comm]
    exact (LinearMap.ker_comp_of_ker_eq_bot _ (pairBaseChangeEquiv (C := C) S).ker).symm) ≪≫ₗ
      (AlgebraTensorModule.rid C S S).ofSubmodule' _

/-- Flat extension of scalars commutes with the kernel of the original relation map. -/
def relationKernelBaseChangeEquiv [Module.Flat C S] :
    S ⊗[C] LinearMap.ker (relationMap x y) ≃ₗ[S]
      LinearMap.ker (relationMap (algebraMap C S x) (algebraMap C S y)) :=
  LinearMap.tensorKerEquiv S S (relationMap x y) ≪≫ₗ relationBaseChangeKernelEquiv x y S

/-- A unit coefficient product annihilates the flat scalar extension of the relation kernel. -/
theorem relationKernelBaseChange_subsingleton [Module.Flat C S]
    (hxy : IsUnit (algebraMap C S (x * y))) :
    Subsingleton (S ⊗[C] LinearMap.ker (relationMap x y)) := by
  let _ : Subsingleton
      (LinearMap.ker (relationMap (algebraMap C S x) (algebraMap C S y))) :=
    Submodule.subsingleton_iff_eq_bot.mpr
      (ker_relationMap_of_isUnit_mul _ _ (by rwa [← map_mul]))
  exact (relationKernelBaseChangeEquiv x y S).subsingleton

end FLT.Mazur.TwoGeneratorRelation
