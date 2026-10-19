/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluExactKernel
public import FLT.Deformations.RepresentationTheory.TrivialQuotientKernel

/-!
# Cyclic kernels for prime torsion quotients

The proved geometric torsion dimension supplies an exact line for any
surjective quotient. Thus every prime quotient used in the Frey target
interface has a cyclic geometric kernel of order p, independently of a
chosen character filtration.
-/

@[expose] public noncomputable section

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
variable (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
variable (hq : Function.Surjective q)

include hq

/-- A surjection from geometric prime torsion has an exact standard line as kernel. -/
theorem exists_exact_torsionKernel_line :
    ∃ i : ZMod p →ₗ[ZMod p] (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p,
      Function.Injective i ∧ LinearMap.range i = LinearMap.ker q := by
  obtain ⟨e⟩ := (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).n_torsion_dimension
    (n := p) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  let e' : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p ≃ₗ[ZMod p]
      ZMod p × ZMod p := { e with map_smul' := ZMod.map_smul e }
  have hdim : Module.finrank (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) = 2 := by
    rw [e'.finrank_eq, Module.finrank_prod]
    simp
  let _ := FiniteDimensional.of_finrank_eq_succ hdim
  have hk := LinearMap.finrank_ker_of_rank_two q hq hdim
  let e₁ : ZMod p ≃ₗ[ZMod p] LinearMap.ker q :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hk.symm)
  let i := (LinearMap.ker q).subtype.comp e₁.toLinearMap
  refine ⟨i, Subtype.val_injective.comp e₁.injective, ?_⟩
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    exact (e₁ x).property
  · intro ht
    refine ⟨e₁.symm ⟨t, ht⟩, ?_⟩
    exact congrArg (fun v : LinearMap.ker q ↦ v.val) (e₁.apply_symm_apply ⟨t, ht⟩)

/-- A surjective prime torsion quotient has exactly p geometric kernel points. -/
theorem torsionKernel_card_prime : Nat.card (torsionKernel E p q) = p := by
  obtain ⟨i, hi, hex⟩ := exists_exact_torsionKernel_line E p q hq
  exact torsionKernel_card_of_exact E p q i hi hex

/-- The geometric kernel of every surjective prime torsion quotient is cyclic. -/
theorem torsionKernel_isAddCyclic_prime : IsAddCyclic (torsionKernel E p q) := by
  obtain ⟨i, hi, hex⟩ := exists_exact_torsionKernel_line E p q hq
  exact torsionKernel_isAddCyclic_of_exact E p q i hi hex

end WeierstrassCurve.Velu
