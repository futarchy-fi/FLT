/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PrincipalFiberFreeness
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Relative flatness from principal fibres

For a finite algebra over a nonfield principal ideal domain, freeness on
each closed base fibre lifts to flatness by localizing at maximal ideals
of the algebra and applying the principal-element flatness criterion.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Module

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]

/-- Freeness of a quotient fibre is preserved by an arbitrary base change. -/
theorem free_quotientFiber_baseChange (I : Ideal B)
    [Module.Free (B ⧸ I) ((B ⧸ I) ⊗[B] A)]
    (C : Type*) [CommRing C] [Algebra B C] :
    Module.Free (C ⧸ I.map (algebraMap B C))
      ((C ⧸ I.map (algebraMap B C)) ⊗[C] (C ⊗[B] A)) := by
  let J := I.map (algebraMap B C)
  let T := C ⧸ J
  let : Algebra (B ⧸ I) T := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower B (B ⧸ I) T := IsScalarTower.of_algebraMap_eq' rfl
  let e := (Algebra.TensorProduct.cancelBaseChange B C T T A).trans
    (Algebra.TensorProduct.cancelBaseChange B (B ⧸ I) T T A).symm
  exact Module.Free.of_equiv e.symm.toLinearEquiv

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Algebra R B] [Algebra R A] [IsScalarTower R B A]
  [Module.Finite R B] [Module.Finite R A] [Module.IsTorsionFree R A]

/-- Free closed fibres imply relative flatness over a nonfield principal ideal domain. -/
theorem flat_of_free_quotientFibers (hR : ¬ IsField R)
    (hfree : ∀ (I : Ideal R) [I.IsMaximal],
      Module.Free (B ⧸ I.map (algebraMap R B))
        ((B ⧸ I.map (algebraMap R B)) ⊗[B] A)) : Module.Flat B A := by
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : Module.Finite B A := Module.Finite.of_restrictScalars_finite R B A
  apply Module.flat_of_isLocalized_maximal B A
    (fun P _ ↦ Localization.AtPrime P ⊗[B] A)
    (fun P _ ↦ TensorProduct.mk B (Localization.AtPrime P) A 1)
  intro P hP
  let C := Localization.AtPrime P
  let N := C ⊗[B] A
  let I := P.under R
  let : I.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  let r := Submodule.IsPrincipal.generator I
  have hrI : Ideal.span {r} = I := Submodule.IsPrincipal.span_singleton_generator I
  have hr0 : r ≠ 0 := by
    intro h
    apply Ring.ne_bot_of_isMaximal_of_not_isField (inferInstance : I.IsMaximal) hR
    rw [← hrI, h, Ideal.span_singleton_zero]
  let b := algebraMap R B r
  let c := algebraMap B C b
  have hJ : (I.map (algebraMap R B)).map (algebraMap B C) = Ideal.span {c} := by
    rw [← hrI, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hfreeN : Module.Free (C ⧸ Ideal.span {c}) ((C ⧸ Ideal.span {c}) ⊗[C] N) := by
    let := hfree I
    have h := free_quotientFiber_baseChange (A := A) (I.map (algebraMap R B)) C
    rw [hJ] at h
    exact h
  let := hfreeN
  have hc : c ∈ (⊥ : Ideal C).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff C P b).mpr
    exact Submodule.IsPrincipal.generator_mem I
  have hreg : IsSMulRegular A b := by
    intro x y hxy
    apply IsSMulRegular.of_ne_zero (M := A) hr0
    simpa only [b, algebraMap_smul] using hxy
  have hregN : IsSMulRegular N c :=
    hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange B A C)
  let : Module.FinitePresentation C N := Module.finitePresentation_of_finite C N
  let : Module.Free C N := Module.free_of_free_quotient_of_smul_regular c hc hregN
  exact Module.Flat.trans B C N

end Module
