/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CharacterFiltrationUnipotent
public import FLT.GaloisRepresentation.HardlyRamified.GeneralInertiaTwo
public import FLT.GaloisRepresentation.HardlyRamified.ResidualReducibleFiltration

/-! # General-prime residual characters are trivial on inertia at two

The original exact filtration is retained. No generic splitting or global
classification of these characters is inferred from this local constraint.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

/-- Every reducible residual HR representation has an actual character filtration
with cyclotomic product and both characters trivial on inertia at two. -/
theorem exists_reducible_character_filtration_inertia_two
    {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
    {k V : Type*} [Field k] [Algebra ℤ_[p] k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    {hV : Module.rank k V = 2} {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified hpodd hV ρ) (hred : ¬ ρ.IsIrreducible) :
    ∃ F : GaloisRep.CharacterFiltration ρ,
      (∀ g : Field.absoluteGaloisGroup ℚ,
        F.χ₁ g 1 * F.χ₂ g 1 = algebraMap ℤ_[p] k
          (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv)) ∧
      ∀ g : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ),
        g ∈ localInertiaGroup twoAdicPlace →
        F.χ₁ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g) = 1 ∧
        F.χ₂ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) g) = 1 := by
  obtain ⟨F, hF⟩ := exists_reducible_character_filtration hρ hred
  refine ⟨F, hF, fun g hg ↦ ?_⟩
  exact F.characters_eq_one_of_sq_zero _
    (hardlyRamified_inertiaTwo_sq_zero_general hpodd hV ρ hρ g hg)

end GaloisRepresentation.IsHardlyRamified
