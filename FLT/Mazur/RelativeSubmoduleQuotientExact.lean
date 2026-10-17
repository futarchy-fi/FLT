/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeSubmoduleQuotient
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# The exact sequence of relative and full correction quotients

When all corrections lie in the boundary module, the cokernel of the relative
inclusion is the unchanged quotient by the boundary module. Its flatness
preserves the relative inclusion under arbitrary scalar extension, including
residue fields. No flatness of that boundary quotient is presumed in applications.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.RelativeSubmoduleQuotient
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (N K : Submodule R M) (hKN : K ≤ N)

/-- Forget corrections and then restrict to the full boundary quotient. -/
def boundaryProjection : (M ⧸ K) →ₗ[R] M ⧸ N :=
  K.mapQ N LinearMap.id hKN

/-- The projection retains the original representative. -/
theorem boundaryProjection_mk (x : M) :
    boundaryProjection N K hKN (K.mkQ x) = N.mkQ x := rfl

/-- Every boundary quotient class has an original representative modulo corrections. -/
theorem boundaryProjection_surjective : Function.Surjective (boundaryProjection N K hKN) := by
  intro x
  obtain ⟨y, rfl⟩ := N.mkQ_surjective x
  exact ⟨K.mkQ y, rfl⟩

/-- The relative inclusion is exactly the kernel of the boundary projection. -/
theorem boundaryProjection_exact :
    Function.Exact (inclusion N K) (boundaryProjection N K hKN) := by
  intro x
  obtain ⟨y, rfl⟩ := K.mkQ_surjective x
  rw [boundaryProjection_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    exact ⟨((K.comap N.subtype).mkQ ⟨y, hy⟩), rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨v, rfl⟩ := (K.comap N.subtype).mkQ_surjective z
    have he : K.mkQ v.val = K.mkQ y := hz
    have hd : v.val - y ∈ K := by
      apply (Submodule.Quotient.mk_eq_zero K).mp
      change K.mkQ (v.val - y) = 0
      rw [map_sub, he, sub_self]
    have hm := N.sub_mem v.property (hKN hd)
    simpa only [sub_sub_cancel] using hm

include hKN in
/-- A flat boundary quotient preserves the relative inclusion even under residue extension. -/
theorem lTensor_injective_of_flat_boundary [Module.Flat R (M ⧸ N)] (S : Type*)
    [AddCommGroup S] [Module R S] :
    Function.Injective ((inclusion N K).lTensor S) :=
  LinearMap.lTensor_injective_of_exact_of_flat (boundaryProjection N K hKN)
    (boundaryProjection_surjective N K hKN) (inclusion N K)
    (inclusion_injective N K) (boundaryProjection_exact N K hKN) S

include hKN in
/-- Under the proved flat-quotient input, ambient tensor vanishing detects relative vanishing. -/
theorem tmul_eq_zero_iff_of_flat_boundary [Module.Flat R (M ⧸ N)]
    (S : Type*) [CommRing S] [Algebra R S] (x : N) :
    (1 ⊗ₜ[R] (K.comap N.subtype).mkQ x : S ⊗[R] (N ⧸ K.comap N.subtype)) = 0 ↔
      (1 ⊗ₜ[R] K.mkQ x.val : S ⊗[R] (M ⧸ K)) = 0 := by
  constructor
  · intro h
    have he := congrArg ((inclusion N K).lTensor S) h
    simpa only [LinearMap.lTensor_tmul, inclusion_mk, map_zero] using he
  · intro h
    apply lTensor_injective_of_flat_boundary N K hKN S
    simpa only [LinearMap.lTensor_tmul, inclusion_mk, map_zero] using h

end FLT.Mazur.RelativeSubmoduleQuotient
