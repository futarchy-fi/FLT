/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontainePointSeparation
public import FLT.Mathlib.RingTheory.ConvolutionTensorPair

/-!
# Recovering an algebra point from a convolution root

A linear functional with convolution cube one is automatically an algebra
map if its reduction at precision greater than one half is an algebra map.
The proof compares its transpose along multiplication with its tensor square,
using separation on the tensor-product coalgebra. Thus this approach enforces
all relations, without choosing a square subsystem of a presentation.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace ThreeAdicPlan

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]
  {A : Type*} [CommRing A] [Bialgebra ℤ_[3] A] [Coalgebra.IsCocomm ℤ_[3] A]

omit [Coalgebra.IsCocomm ℤ_[3] A] in
/-- A convolution cube root reducing to a unital map preserves the unit. -/
theorem conv_cube_root_map_one {t : ℚ} (ht : 1 / 2 < t)
    (F : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E)) (hF : F ^ 3 = 1)
    (u : A →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E t)
    (hcompat : ∀ a, Ideal.Quotient.mk (threeAdicValuationIdeal E t) (F a) = u a) :
    F 1 = 1 := by
  let η := (Bialgebra.unitBialgHom ℤ_[3] A).toCoalgHom
  have hpow : toConv (F.ofConv.comp η.toLinearMap) ^ 3 = 1 := by
    apply WithConv.ext
    rw [← LinearMap.convPow_comp_coalgHom, hF, LinearMap.convOne_precomp_coalgHom]
  have heq := conv_eq_one_of_cube_eq_one_of_close E ht _ hpow (by
    intro r
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk _ (F (algebraMap ℤ_[3] A r) - algebraMap ℤ_[3] _ r) = 0
    rw [map_sub, hcompat]
    simp)
  have h := congrArg (fun f : WithConv (ℤ_[3] →ₗ[ℤ_[3]] ThreeAdicIntegers E) ↦ f 1) heq
  have hη : η 1 = 1 := map_one (Bialgebra.unitBialgHom ℤ_[3] A)
  change F (η 1) = (1 : WithConv (ℤ_[3] →ₗ[ℤ_[3]] ThreeAdicIntegers E)) 1 at h
  simpa only [hη, LinearMap.convOne_apply,
    CommSemiring.counit_apply, map_one] using h

/-- A convolution cube root reducing to an algebra map preserves products.
Separation is applied to the whole tensor-product coalgebra. -/
theorem conv_cube_root_map_mul {t : ℚ} (ht : 1 / 2 < t)
    (F : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E)) (hF : F ^ 3 = 1)
    (u : A →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E t)
    (hcompat : ∀ a, Ideal.Quotient.mk (threeAdicValuationIdeal E t) (F a) = u a)
    (a b : A) : F (a * b) = F a * F b := by
  let μ := Bialgebra.mulCoalgHom ℤ_[3] A
  let G := toConv (F.ofConv.comp μ.toLinearMap)
  let H := LinearMap.convTensorPair F F
  have hG : G ^ 3 = 1 := by
    apply WithConv.ext
    rw [← LinearMap.convPow_comp_coalgHom, hF, LinearMap.convOne_precomp_coalgHom]
  have hH : H ^ 3 = 1 := by
    change LinearMap.convTensorPair F F ^ 3 = 1
    rw [← LinearMap.convTensorPair_pow, hF, LinearMap.convTensorPair_one]
  have heq := conv_eq_of_cube_eq_one_of_close E ht G H hG hH (by
    intro z
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      change Ideal.Quotient.mk _ (F (x * y) - F x * F y) = 0
      simp only [map_sub, map_mul, hcompat, sub_self]
    | add x y hx hy =>
      change Ideal.Quotient.mk _ ((G - H).ofConv (x + y)) = 0
      rw [map_add, map_add, hx, hy, add_zero])
  exact congrArg (fun f : WithConv (A ⊗[ℤ_[3]] A →ₗ[ℤ_[3]] ThreeAdicIntegers E) ↦
    f (a ⊗ₜ[ℤ_[3]] b)) heq

/-- A nearby linear convolution cube root uniquely determines an algebra
point. No hypothesis that selected polynomial relations generate is required. -/
theorem exists_algHom_of_conv_cube_root {t : ℚ} (ht : 1 / 2 < t)
    (F : WithConv (A →ₗ[ℤ_[3]] ThreeAdicIntegers E)) (hF : F ^ 3 = 1)
    (u : A →ₐ[ℤ_[3]] ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E t)
    (hcompat : ∀ a, Ideal.Quotient.mk (threeAdicValuationIdeal E t) (F a) = u a) :
    ∃ v : A →ₐ[ℤ_[3]] ThreeAdicIntegers E,
      v.toLinearMap = F.ofConv ∧
      (Ideal.Quotient.mkₐ ℤ_[3] (threeAdicValuationIdeal E t)).comp v = u := by
  let v := AlgHom.ofLinearMap F.ofConv (conv_cube_root_map_one E ht F hF u hcompat)
    (conv_cube_root_map_mul E ht F hF u hcompat)
  exact ⟨v, rfl, AlgHom.ext hcompat⟩

end ThreeAdicPlan
