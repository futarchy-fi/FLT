/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Noetherian.Orzech

/-!
# A presentation criterion from a spanning family of the right size

A surjection from a module spanned by n elements onto a free module of
rank n is injective. No freeness or absence of torsion is assumed for
the source: the composite from R^n is already an isomorphism.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R M N ι : Type*} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Free R N] [Module.Finite R N] [Fintype ι]

/-- A spanning family of the target rank proves injectivity of an existing surjection. -/
theorem bijective_of_spanning_card (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (hcard : Fintype.card ι = Module.finrank R N) :
    Function.Bijective f := by
  let g := Fintype.linearCombination R v
  have hg : Function.Surjective g :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).mp hv
  have hfg : Function.Bijective (f.comp g) :=
    OrzechProperty.bijective_of_surjective_of_finrank_le (f.comp g) (hf.comp hg) (by
      simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one]
      exact hcard.le)
  refine ⟨?_, hf⟩
  intro x y hxy
  obtain ⟨x', rfl⟩ := hg x
  obtain ⟨y', rfl⟩ := hg y
  exact congrArg g (hfg.injective hxy)

end ThreeAdicPlan
