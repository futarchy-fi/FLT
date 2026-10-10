/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReducedFiberBasis

/-!
# Constant fiber dimension over a reduced local ring

Lift a basis from the closed fiber by Nakayama. The dimension of all other
field fibers then rules out relations, giving an actual finite free module.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.ReducedLocalConstantFiberRank

universe u
variable {R M : Type u} [CommRing R] [IsReduced R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Constant field-fiber dimension makes a finite module over a reduced local ring free. -/
theorem free_of_constant_field_dimension (n : ℕ)
    (hd : ∀ (K : Type u) [Field K] [Algebra R K],
      Module.finrank K (K ⊗[R] M) = n) : Module.Free R M := by
  classical
  let k := IsLocalRing.ResidueField R
  let b := Module.finBasis k (k ⊗[R] M)
  have hs : Function.Surjective (TensorProduct.mk R k M 1) :=
    TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  choose v hv using fun i ↦ hs (b i)
  have hsp : Submodule.span R (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  let f := Finsupp.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hsp
  have hb : Function.Bijective f :=
    ReducedFiberBasis.bijective_of_surjective_of_fiber_dimension f hf (by
      intro p _
      simpa only [Fintype.card_fin, hd k] using hd p.ResidueField)
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f hb)

end FLT.Mazur.ReducedLocalConstantFiberRank
