/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatQuotientIdealFiber
public import FLT.Mazur.RelativeFiberNakayama

/-!
# Lifting a regular equation from a coefficient fiber

For a finitely presented ideal with base-flat ambient and quotient, a regular
fiber equation lifts to a regular generator. The fiber ideal is the actual
extended ideal; no flatness of the coefficient quotient is required.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- Multiplication by an element of an ideal, with codomain the ideal itself. -/
def idealElementMap (I : Ideal B) (a : B) (ha : a ∈ I) : B →ₗ[B] I :=
  (LinearMap.mulRight B a).codRestrict I (fun b ↦ I.mul_mem_left b ha)

/-- Tensoring this multiplication map gives multiplication by the fiber equation. -/
theorem idealElementMap_fiber_mul (I : Ideal B) (a : B) (ha : a ∈ I)
    (C : Type*) [CommRing C] [Algebra R C] (x : C ⊗[R] B) :
    (I.subtype.restrictScalars R).lTensor C
      (((idealElementMap I a ha).restrictScalars R |>.lTensor C) x) =
      x * (1 ⊗ₜ[R] a) := by
  induction x with
  | tmul c b =>
    change c ⊗ₜ[R] (b * a) = (c ⊗ₜ[R] b) * (1 ⊗ₜ[R] a)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add x y hx hy => simp only [map_add, add_mul, hx, hy]

/-- A regular generator of the actual fiber ideal makes the fiber equation map bijective. -/
theorem idealElementMap_fiber_bijective (I : Ideal B) [Module.Flat R (B ⧸ I)]
    (a : B) (ha : a ∈ I) (C : Type*) [CommRing C] [Algebra R C]
    (hr : IsRegular (1 ⊗ₜ[R] a : C ⊗[R] B))
    (hI : I.map (Algebra.TensorProduct.includeRight (R := R) (A := C)) =
      Ideal.span {1 ⊗ₜ[R] a}) :
    Function.Bijective ((idealElementMap I a ha).restrictScalars R |>.lTensor C) := by
  constructor
  · intro x y h
    apply hr.right
    simpa only [idealElementMap_fiber_mul] using
      congrArg ((I.subtype.restrictScalars R).lTensor C) h
  · intro x
    have hx := (flatQuotientIdealFiberEquiv I C x).property
    change (I.subtype.restrictScalars R).lTensor C x ∈ I.map _ at hx
    rw [hI, Ideal.mem_span_singleton] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ideal_fiber_inclusion_injective I C ?_⟩
    rw [idealElementMap_fiber_mul]
    change y * (1 ⊗ₜ[R] a) = (flatQuotientIdealFiberEquiv I C x).val
    exact (mul_comm _ _).trans hy.symm

/-- A regular equation on a coefficient fiber lifts for a finitely presented flat ideal. -/
theorem regular_generator_of_flat_quotient_fiber (J : Ideal R)
    (hJ : J.map (algebraMap R B) ≤ Ideal.jacobson ⊥)
    (I : Ideal B) [Module.Flat R B] [Module.Flat R (B ⧸ I)]
    [Module.FinitePresentation B I] (a : B) (ha : a ∈ I)
    (hr : IsRegular (1 ⊗ₜ[R] a : (R ⧸ J) ⊗[R] B))
    (hI : I.map (Algebra.TensorProduct.includeRight (R := R) (A := R ⧸ J)) =
      Ideal.span {1 ⊗ₜ[R] a}) : IsRegular a ∧ I = Ideal.span {a} := by
  let f := idealElementMap I a ha
  let _ : Module.Flat R I := ideal_flat_of_flat_quotient I
  have hf := idealElementMap_fiber_bijective I a ha (R ⧸ J) hr hI
  have hs : Function.Surjective f := surjective_of_coefficient_fiber J hJ f hf.2
  have hi : Function.Injective f := (bijective_of_coefficient_fiber J hJ f hs hf.1).1
  constructor
  · rw [← isRightRegular_iff_isRegular]
    intro x y h
    exact hi (Subtype.ext h)
  · apply le_antisymm
    · intro b hb
      obtain ⟨c, hc⟩ := hs ⟨b, hb⟩
      apply Ideal.mem_span_singleton.mpr
      exact ⟨c, (congrArg Subtype.val hc).symm.trans (mul_comm c a)⟩
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)

end FLT.Mazur.FCurve
