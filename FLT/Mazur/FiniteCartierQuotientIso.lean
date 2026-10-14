/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCartierQuotientComparison
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Recovering the finite algebra from its actual Cartier quotient map

The quotient map is induced by the original algebra map. Its bijectivity
and the regular pulled parameter construct an inverse to that same map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCartierComparison

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
local notation "f" => algebraMap R A

/-- The actual map on the original parameter quotients. -/
def parameterQuotientMap (t : R) :
    (R ⧸ Ideal.span {t}) →+* (A ⧸ Ideal.span {f t}) :=
  Ideal.quotientMap (Ideal.span {f t}) (f) (by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton_self (f t))

/-- The quotient comparison retains the original map on every representative. -/
@[simp] theorem parameterQuotientMap_mk (t a : R) :
    parameterQuotientMap (A := A) t (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (f a) := rfl

/-- Bijectivity of the original quotient comparison recovers the whole finite map. -/
theorem bijective_of_parameterQuotientMap [IsNoetherianRing R] [Module.Finite R A]
    (t : R) (ht : t ∈ Ideal.jacobson (⊥ : Ideal R))
    (hreg : f t ∈ nonZeroDivisors A)
    (hq : Function.Bijective (parameterQuotientMap (A := A) t)) :
    Function.Bijective (f) := by
  apply bijective_of_mod_parameter t ht hreg
  · intro b
    obtain ⟨c, hc⟩ := hq.2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨a, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ?_⟩
    exact hc.symm
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hq.1
    rw [parameterQuotientMap_mk, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- The inverse preserves the original algebra structure and the original comparison map. -/
def algebraEquivOfParameterQuotientMap [IsNoetherianRing R] [Module.Finite R A]
    (t : R) (ht : t ∈ Ideal.jacobson (⊥ : Ideal R))
    (hreg : f t ∈ nonZeroDivisors A)
    (hq : Function.Bijective (parameterQuotientMap (A := A) t)) : R ≃ₐ[R] A :=
  AlgEquiv.ofBijective (Algebra.ofId R A)
    (bijective_of_parameterQuotientMap t ht hreg hq)

/-- The recovered algebra isomorphism is the original map on each scalar. -/
theorem algebraEquivOfParameterQuotientMap_apply [IsNoetherianRing R] [Module.Finite R A]
    (t : R) (ht : t ∈ Ideal.jacobson (⊥ : Ideal R))
    (hreg : f t ∈ nonZeroDivisors A)
    (hq : Function.Bijective (parameterQuotientMap (A := A) t)) (r : R) :
    algebraEquivOfParameterQuotientMap t ht hreg hq r = f r := rfl

/-- At a point of the divisor, membership in the local maximal ideal suffices. -/
theorem local_bijective_of_parameterQuotientMap [IsLocalRing R]
    [IsNoetherianRing R] [Module.Finite R A] (t : R)
    (ht : t ∈ IsLocalRing.maximalIdeal R) (hreg : f t ∈ nonZeroDivisors A)
    (hq : Function.Bijective (parameterQuotientMap (A := A) t)) :
    Function.Bijective (f) :=
  bijective_of_parameterQuotientMap t (IsLocalRing.maximalIdeal_le_jacobson ⊥ ht) hreg hq

end FLT.Mazur.FiniteCartierComparison
