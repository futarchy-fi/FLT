/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.AdicSeparatedInjectivity
public import FLT.Mathlib.RingTheory.Flat.QuotientBaseInjectivity
public import FLT.Mathlib.RingTheory.Flat.FlatCokernelIdealCriterion

/-! # The local flatness criterion for a cokernel -/

@[expose] public section

namespace Module.Flat

variable {R S N M Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] [Module.Finite S N]
  [AddCommGroup M] [Module R M] [Flat R M] [AddCommGroup Q] [Module R Q]

include S

/-- In a right exact sequence with flat middle term and finite Noetherian-local
source, residual injectivity implies both injectivity and a flat cokernel. -/
theorem injective_and_flat_of_local_residue (f : N →ₗ[R] M) (g : M →ₗ[R] Q)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hf : Function.Injective (f.lTensor (R ⧸ IsLocalRing.maximalIdeal R))) :
    Function.Injective f ∧ Flat R Q :=
  ⟨injective_of_local_residue_injective (S := S) f hf,
    of_exact_of_lTensor_quotient_injective f g hex hg
      (lTensor_quotient_injective_of_local_residue (S := S) f hf)⟩

end Module.Flat
