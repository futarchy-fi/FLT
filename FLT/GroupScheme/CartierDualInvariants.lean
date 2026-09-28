/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualKernelInclusion
public import FLT.GroupScheme.HopfTorsor
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Invariants and annihilators for integral Cartier duality

Faithfully flat descent identifies the original quotient coordinates with
the functions invariant under translation by the kernel. The perfect integral
Cartier pairing expresses these invariants as the annihilator of the dual
augmentation ideal.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.CartierDual

variable {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N]
  [Module.Projective R M] [Module.Projective R N]

/-- Products of integral dual functionals separate tensors of finite projective modules. -/
theorem tensor_eq_of_forall_pairing {x y : M ⊗[R] N}
    (h : ∀ (φ : CartierDual R M) (ψ : CartierDual R N),
      tensorEquiv R M N (φ ⊗ₜ[R] ψ) x = tensorEquiv R M N (φ ⊗ₜ[R] ψ) y) : x = y := by
  apply (Module.evalEquiv R (M ⊗[R] N)).injective
  ext f
  obtain ⟨t, rfl⟩ := (tensorEquiv R M N).surjective f
  change tensorEquiv R M N t x = tensorEquiv R M N t y
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => exact h φ ψ
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]

variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]
  [Module.Finite R A] [Module.Finite R B] [Module.Projective R A] [Module.Projective R B]

/-- Pairing a coaction with two functionals is convolution with the transposed map. -/
theorem tensor_pairing_coaction (f : A →ₐc[R] B)
    (φ : CartierDual R A) (ψ : CartierDual R B) (a : A) :
    tensorEquiv R A B (φ ⊗ₜ[R] ψ)
      (Algebra.TensorProduct.map (AlgHom.id R A) f.toAlgHom (Coalgebra.comul a)) =
        (φ * bialgMap f ψ) a := by
  rw [LinearMap.convMul_apply]
  generalize Coalgebra.comul (R := R) a = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end HopfAlgebra.CartierDual

namespace ThreeAdicPlan

open HopfAlgebra.CartierDual

variable {R : Type} [CommRing R] [Algebra R ℚ]
  {A H Q : FiniteFlatObject R}

/-- Quotient coordinates are exactly the functions invariant under kernel translation. -/
theorem FiniteFlatExtension.exists_quotient_preimage_iff (E : FiniteFlatExtension A H Q)
    (h : H.model.CoordinateRing) :
    (∃ q, E.quotient q = h) ↔
      Algebra.TensorProduct.map (AlgHom.id R H.model.CoordinateRing) E.inclusion.toAlgHom
        (Coalgebra.comul h) = h ⊗ₜ[R] (1 : A.model.CoordinateRing) := by
  let := E.quotient.toAlgHom.toRingHom.toAlgebra
  let := E.quotientFaithfullyFlat
  have hex := Algebra.IsEffective.of_faithfullyFlat
    Q.model.CoordinateRing H.model.CoordinateRing
  change (h ∈ Set.range (Algebra.linearMap Q.model.CoordinateRing H.model.CoordinateRing)) ↔ _
  rw [← hex h, Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
  constructor
  · intro hh
    rw [← E.torsorEquivSecond, ← hh]
    exact E.torsorEquiv.commutes h
  · intro hh
    apply E.torsorEquiv.injective
    rw [E.torsorEquivSecond, hh]
    exact E.torsorEquiv.commutes h

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- An element annihilating the dual augmentation ideal comes from the original quotient. -/
theorem FiniteFlatExtension.exists_quotient_preimage_of_annihilates
    (E : FiniteFlatExtension A H Q) (h : H.model.CoordinateRing)
    (hh : ∀ (φ : HopfAlgebra.CartierDual R H.model.CoordinateRing),
      φ ∈ HopfAlgebra.augmentationIdeal E.inclusion.cartierDual → φ h = 0) :
    ∃ q, E.quotient q = h := by
  apply E.exists_quotient_preimage_iff h |>.mpr
  apply tensor_eq_of_forall_pairing
  intro φ ψ
  rw [tensor_pairing_coaction, tensorEquiv_tmul]
  let ψ₀ : HopfAlgebra.CartierDual R A.model.CoordinateRing := ψ - ψ 1 • 1
  have hψ₀ : ψ₀ ∈ RingHom.ker
      (Bialgebra.counitAlgHom R A.cartierDual.model.CoordinateRing).toRingHom := by
    change ψ₀ 1 = 0
    simp [ψ₀]
  have hm := hh (φ * bialgMap E.inclusion ψ₀)
    (Ideal.mul_mem_left _ φ (Ideal.mem_map_of_mem _ hψ₀))
  have he : φ * bialgMap E.inclusion ψ₀ =
      φ * bialgMap E.inclusion ψ - ψ 1 • φ := by
    simp [ψ₀, mul_sub]
  rw [he] at hm
  change (φ * bialgMap E.inclusion ψ) h - ψ 1 * φ h = 0 at hm
  exact (sub_eq_zero.mp hm).trans (mul_comm _ _)

end ThreeAdicPlan
