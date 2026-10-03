/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ModThreeFiltration

/-! # The actual mod-three extension cocycle

A lift of one along the trivial quotient gives a cyclotomic-valued
1-cocycle in the original module. Its vanishing is not assumed.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified

/-- The nonsplit extension data of the original mod-three representation. -/
theorem mod_three_extension_cocycle
    {k V : Type*} [Field k] [Finite k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (e : V) (b : Field.absoluteGaloisGroup ℚ → V),
      Function.Surjective π ∧ Module.finrank k (LinearMap.ker π) = 1 ∧ π e = 1 ∧
      (∀ g x, π (ρ g x) = π x) ∧
      (∀ g, b g = ρ g e - e) ∧ (∀ g, π (b g) = 0) ∧
      (∀ g h, b (g * h) = algebraMap ℤ_[3] k
        (cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv) • b h + b g) ∧
      ∀ g, b g = 0 ↔ ρ g e = e := by
  obtain ⟨π, hπ, hdim, hinv, hker⟩ := hρ.mod_three_cyclotomic_filtration hV
  obtain ⟨e, he⟩ := hπ 1
  let b := fun g ↦ ρ g e - e
  have hb (g : Field.absoluteGaloisGroup ℚ) : π (b g) = 0 := by
    dsimp [b]
    rw [map_sub, hinv, sub_self]
  refine ⟨π, e, b, hπ, hdim, he, hinv, fun _ ↦ rfl, hb, ?_, ?_⟩
  · intro g h
    rw [← hker g (b h) (hb h)]
    dsimp [b]
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel
  · intro g
    exact sub_eq_zero

end GaloisRepresentation.IsHardlyRamified
