/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarOrbitQuotientComparison

/-!
# Full coefficient tests for original orbit arrows

A test of the original scalar tensor factors through the orbit relation exactly
when the two copies of every full invariant agree. The factor is constructed
uniquely for arbitrary coefficient rings, retaining their nilpotents.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarOrbitTensorComparison
open FiniteGroupQuotient
variable (G R A : Type*) [Group G] [CommRing R] [CommRing A]
  [MulSemiringAction G A] [Algebra R A] [Algebra R (invariantRing G A)]
  [IsScalarTower R (invariantRing G A) A]
local notation "S" => invariantRing G A
local notation "C" => A ⊗[R] A
variable {B : Type*} [CommRing B] (testMap : A ⊗[R] A →+* B)

omit [Algebra R S] [IsScalarTower R S A] in
/-- Full invariant equality is precisely vanishing of the actual balancing ideal. -/
theorem balancingIdeal_le_ker_iff : balancingIdeal G R A ≤ RingHom.ker testMap ↔
    ∀ s : S, testMap (s.val ⊗ₜ[R] (1 : A)) = testMap (1 ⊗ₜ[R] s.val) := by
  rw [balancingIdeal, Ideal.span_le]
  constructor
  · intro h s
    have hs := h (Set.mem_range_self s)
    change testMap (s.val ⊗ₜ[R] (1 : A) - 1 ⊗ₜ[R] s.val) = 0 at hs
    rwa [map_sub, sub_eq_zero] at hs
  · intro h x hx
    obtain ⟨s, rfl⟩ := hx
    change testMap (s.val ⊗ₜ[R] (1 : A) - 1 ⊗ₜ[R] s.val) = 0
    rw [map_sub, h s, sub_self]

variable [Finite G] (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
include hfree

/-- Exact invariant agreement constructs the unique full orbit arrow on a coefficient test. -/
theorem existsUnique_lift_iff :
    (∃! ψ : (G → A) →+* B, ψ.comp (comparison G R A).toRingHom = testMap) ↔
      ∀ s : S, testMap (s.val ⊗ₜ[R] (1 : A)) = testMap (1 ⊗ₜ[R] s.val) := by
  rw [← balancingIdeal_le_ker_iff, ← comparison_ker_eq_balancingIdeal G R A hfree]
  constructor
  · rintro ⟨ψ, hψ, _⟩ t ht
    rw [← hψ]
    change ψ (comparison G R A t) = 0
    change comparison G R A t = 0 at ht
    rw [ht, map_zero]
  · intro h
    let f := (comparison G R A).toRingHom
    have hf : Function.Surjective f := comparison_surjective G R A hfree
    exact ⟨f.liftOfSurjective hf ⟨testMap, h⟩,
      f.liftOfSurjective_comp hf ⟨testMap, h⟩,
      fun ψ hψ ↦ f.eq_liftOfSurjective hf testMap h ψ hψ⟩

variable [Algebra R B] (u v : A →ₐ[R] B)

/-- The two original endpoint maps lift exactly when all full invariants have equal values. -/
theorem existsUnique_endpoint_lift_iff :
    (∃! ψ : (G → A) →+* B, ψ.comp (comparison G R A).toRingHom =
      (Algebra.TensorProduct.productMap u v).toRingHom) ↔
      ∀ s : S, u s.val = v s.val := by
  rw [existsUnique_lift_iff G R A _ hfree]
  simp only [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

end FLT.Mazur.ScalarOrbitTensorComparison
