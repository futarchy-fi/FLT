/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedSum

/-!
# Units for tensor-power section multiplication

The right unit law is proved as an equality of sheaf morphisms. Thus it
applies to arbitrary sections, without assuming global pure tensors span.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedMultiplication
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
open ModuleSheafTensorAssociator
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules)

/-- Transport a section between equal tensor degrees. -/
def cast {m n : ℕ} (h : m = n) (U : X.Opens) :
    Piece L U m →ₗ[Γ(X, U)] Piece L U n :=
  ((eqToIso (congrArg (tensorPower L) h)).hom.val.app (.op U)).hom

@[simp]
lemma cast_rfl (n : ℕ) (U : X.Opens) (s : Piece L U n) :
    cast L rfl U s = s := rfl

/-- Degree-zero multiplication on the left is scalar multiplication. -/
lemma zero_mul (n : ℕ) (U : X.Opens) (r : Γ(X, U)) (s : Piece L U n) :
    mul L U 0 n r s = cast L (Nat.zero_add n).symm U (r • s) := by
  change (eqToIso (congrArg (tensorPower L) (Nat.zero_add n).symm)).hom.app U
    ((leftUnitor _).hom.app U (pure _ _ U r s)) = _
  rw [leftUnitor_pure]
  rfl

/-- Addition of degree zero agrees with the right unit morphism. -/
lemma addIso_zero (n : ℕ) :
    (tensorPowerAddIso L n 0).hom =
      (comm (tensorPower L n) (structureModule X)).hom ≫
        (leftUnitor (tensorPower L n)).hom := by
  induction n with
  | zero =>
    apply ModuleSheafTensor.hom_ext
    intro U r s
    change (leftUnitor _).hom.app U (pure _ _ U r s) =
      (leftUnitor _).hom.app U ((comm _ _).hom.app U (pure _ _ U r s))
    simp only [comm_hom_pure, leftUnitor_pure]
    change Γ(X, U) at r s
    change r * s = s * r
    exact _root_.mul_comm r s
  | succ n ih =>
    apply left_hom_ext
    intro U s t r
    change (ModuleSheafTensor.map (𝟙 L) (tensorPowerAddIso L n 0).hom).app U
      ((ModuleSheafTensorAssociator.associator _ _ _).hom.app U (pure _ _ U (pure _ _ U s t) r)) =
      (leftUnitor _).hom.app U ((comm _ _).hom.app U
        (pure _ _ U (pure _ _ U s t) r))
    rw [associator_hom_pure, ModuleSheafTensor.map_pure, ih]
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      comm_hom_pure, leftUnitor_pure, Scheme.Modules.Hom.id_app,
      ConcreteCategory.id_apply]
    change pure L (tensorPower L n) U s
      ((leftUnitor _).hom.app U ((comm _ _).hom.app U (pure _ _ U t r))) = _
    rw [comm_hom_pure, leftUnitor_pure]
    exact ((pairing L (tensorPower L n)).app U s).map_smul r t

/-- Degree-zero multiplication on the right is scalar multiplication. -/
lemma mul_zero (n : ℕ) (U : X.Opens) (s : Piece L U n) (r : Γ(X, U)) :
    mul L U n 0 s r = r • s := by
  rw [mul_apply, addIso_zero]
  change (leftUnitor _).hom.app U ((comm _ _).hom.app U (pure _ _ U s r)) = _
  rw [comm_hom_pure, leftUnitor_pure]

end FLT.Mazur.SectionGradedMultiplication

namespace FLT.Mazur.SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open SectionGradedMultiplication
variable {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)

/-- The multiplicative unit is the structure sheaf's unit in degree zero. -/
def unit : Sections L U := of L U 0 (1 : Γ(X, U))

/-- Homogeneous insertion absorbs transport of the degree. -/
lemma of_cast {m n : ℕ} (h : m = n) (s : Piece L U m) :
    of L U n (cast L h U s) = of L U m s := by
  subst n
  rfl

/-- The degree-zero unit acts identically on every finite sum of sections. -/
lemma unit_product (a : Sections L U) : product L U (unit L U) a = a := by
  induction a using DirectSum.induction_on with
  | zero => exact map_zero _
  | of n s =>
    change product L U (of L U 0 (1 : Γ(X, U))) (of L U n s) = of L U n s
    rw [product_of, zero_mul, one_smul, of_cast]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Every finite sum of sections has the same right unit. -/
lemma product_unit (a : Sections L U) : product L U a (unit L U) = a := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n s =>
    change product L U (of L U n s) (of L U 0 (1 : Γ(X, U))) = of L U n s
    rw [product_of, mul_zero, one_smul]
    rfl
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

end FLT.Mazur.SectionGradedSum
