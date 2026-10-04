/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualMaps
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Data.ZMod.Basic

/-! # A square-zero coefficient reduction with a nonlifting quadratic character -/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual.LinearLiftCounterexample

/-- Reduction modulo eight, with square-zero kernel inside the ring modulo sixteen. -/
def reduction : ZMod 16 →+* ZMod 8 := ZMod.castHom (by decide) _

instance coefficientAlgebra : Algebra (ZMod 16) (ZMod 8) := reduction.toAlgebra

/-- The coefficient reduction as a map over the original base ring. -/
def quotientMap : ZMod 16 →ₐ[ZMod 16] ZMod 8 := Algebra.ofId _ _

/-- The specified coefficient reduction is surjective. -/
theorem quotientMap_surjective : Function.Surjective quotientMap :=
  ZMod.castHom_surjective (by decide)

/-- The actual kernel has square zero. -/
theorem quotientMap_kernel_square : RingHom.ker quotientMap ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  change a * b = 0
  have h : ∀ a b : ZMod 16, reduction a = 0 → reduction b = 0 → a * b = 0 := by decide
  exact h a b ha hb

/-- Two annihilates the actual square-zero kernel. -/
theorem quotientMap_kernel_two (a : ZMod 16) (ha : a ∈ RingHom.ker quotientMap) :
    2 • a = 0 := by
  have h : ∀ a : ZMod 16, reduction a = 0 → 2 • a = 0 := by decide
  exact h a ha

/-- The constant group of order two in multiplicative notation. -/
abbrev Group := Multiplicative (ZMod 2)
/-- Its finite free group algebra over the thickened coefficient ring. -/
abbrev GroupRing := MonoidAlgebra (ZMod 16) Group
/-- The dual group algebra is the original constant-group coordinate Hopf algebra. -/
abbrev Coordinates := CartierDual (ZMod 16) GroupRing

instance coordinatesFree : Module.Free (ZMod 16) Coordinates :=
  Module.Free.of_equiv (linearEquiv (R := ZMod 16) (A := GroupRing)).symm

/-- The order-two character whose generator is three modulo eight. -/
def character : Group →* ZMod 8 where
  toFun g := if g = 1 then 1 else 3
  map_one' := by simp
  map_mul' g h := by
    exact (by decide : ∀ g h : Group,
      (if g * h = 1 then (1 : ZMod 8) else 3) =
        (if g = 1 then 1 else 3) * (if h = 1 then 1 else 3)) g h

/-- The genuine reduced dual character, transported along integral biduality. -/
def reducedCharacter : CartierDual (ZMod 16) Coordinates →ₐ[ZMod 16] ZMod 8 :=
  (MonoidAlgebra.lift _ _ _ character).comp
    (bidualAlgEquiv (R := ZMod 16) (A := GroupRing)).symm.toAlgHom

/-- A linear lift of its coefficients; this map is not claimed multiplicative. -/
def liftedCharacter : CartierDual (ZMod 16) Coordinates →ₗ[ZMod 16] ZMod 16 :=
  ((Finsupp.linearCombination (ZMod 16) (fun g : Group ↦ if g = 1 then 1 else 3)).comp
    (MonoidAlgebra.coeffLinearEquiv (ZMod 16)).toLinearMap).comp
    (bidualAlgEquiv (R := ZMod 16) (A := GroupRing)).symm.toLinearMap

/-- These linear coefficients reduce to the specified algebra character. -/
theorem liftedCharacter_reduction :
    quotientMap.toLinearMap.comp liftedCharacter = reducedCharacter.toLinearMap := by
  apply LinearMap.ext
  intro a
  obtain ⟨a, rfl⟩ := (bidualAlgEquiv (R := ZMod 16) (A := GroupRing)).surjective a
  change quotientMap (Finsupp.linearCombination _ _
    ((bidualAlgEquiv.symm (bidualAlgEquiv a) : GroupRing).coeff)) =
      MonoidAlgebra.lift _ _ _ character (bidualAlgEquiv.symm (bidualAlgEquiv a))
  simp only [AlgEquiv.symm_apply_apply]
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    change quotientMap (Finsupp.linearCombination _ _ (Finsupp.single g 1)) =
      MonoidAlgebra.lift _ _ _ character (MonoidAlgebra.single g 1)
    rw [Finsupp.linearCombination_single, MonoidAlgebra.lift_single, one_smul, one_smul]
    simp only [character, MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs <;> rfl
  | add a b ha hb => simp only [MonoidAlgebra.coeff_add, map_add, ha, hb]
  | smul r a ha => simp only [MonoidAlgebra.coeff_smul, map_smul, ha]

/-- The original constant-group generator is already an algebra point over the thickening. -/
def generator : Coordinates →ₐ[ZMod 16] ZMod 16 :=
  (Pi.evalAlgHom _ (fun _ : Group ↦ ZMod 16) (Multiplicative.ofAdd 1)).comp
    (groupAlgebraEquiv (ZMod 16) Group).toAlgHom

/-- In the double dual this point is the original group-algebra basis vector. -/
theorem generator_linear : WithConv.toConv generator.toLinearMap =
    bidualAlgEquiv (R := ZMod 16) (MonoidAlgebra.single (Multiplicative.ofAdd 1 : Group) 1) := rfl

/-- Its square is the augmentation, already before any reduction. -/
theorem generator_square : (WithConv.toConv generator ^ 2).ofConv =
    (1 : WithConv (Coordinates →ₐ[ZMod 16] ZMod 16)).ofConv := by
  apply AlgHom.toLinearMap_injective
  apply (WithConv.linearEquiv (ZMod 16) _).symm.injective
  change WithConv.toConv _ = WithConv.toConv _
  rw [AlgHom.toLinearMap_convPow, generator_linear, ← map_pow]
  have hg : (Multiplicative.ofAdd 1 : Group) ^ 2 = 1 := by decide
  simp only [MonoidAlgebra.single_pow, hg, one_pow]
  exact map_one (bidualAlgEquiv (R := ZMod 16) (A := GroupRing))

/-- The linear pairing reads the chosen lift three, whose square is not one. -/
theorem liftedCharacter_generator :
    liftedCharacter (WithConv.toConv generator.toLinearMap) = 3 := by
  rw [generator_linear]
  change Finsupp.linearCombination _ _
    (bidualAlgEquiv.symm (bidualAlgEquiv _) : GroupRing).coeff = _
  simp only [AlgEquiv.symm_apply_apply, MonoidAlgebra.coeff_single,
    Finsupp.linearCombination_single, one_smul]
  decide

end HopfAlgebra.CartierDual.LinearLiftCounterexample
