/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ModThreeProved
public import FLT.Deformations.RepresentationTheory.TrivialQuotientKernel

/-!
# The actual cyclotomic-by-trivial mod-three filtration

Integral sorting supplies the quotient of the original representation. Its
kernel is a line with cyclotomic action, including for nonsplit extensions.
No compatible family or invariant complement is constructed.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified

/-- The original mod-three representation is a cyclotomic-by-trivial extension. -/
theorem mod_three_cyclotomic_filtration
    {k V : Type*} [Field k] [Finite k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ π : V →ₗ[k] k, Function.Surjective π ∧ Module.finrank k (LinearMap.ker π) = 1 ∧
      (∀ (g : Field.absoluteGaloisGroup ℚ) (x : V), π (ρ g x) = π x) ∧
      ∀ (g : Field.absoluteGaloisGroup ℚ) (x : V), π x = 0 →
        ρ g x = algebraMap ℤ_[3] k
          (cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv) • x := by
  obtain ⟨π, hπ, hinv⟩ := hρ.mod_three_from_sorting hV
  have hdim := Module.finrank_eq_of_rank_eq hV
  refine ⟨π, hπ, LinearMap.finrank_ker_of_rank_two π hπ hdim, hinv, ?_⟩
  intro g x hx
  have h := LinearMap.apply_ker_eq_det_smul π hπ hdim (ρ g) (hinv g) x hx
  exact h.trans (congrArg (fun a : k ↦ a • x) (hρ.det g))

end GaloisRepresentation.IsHardlyRamified
