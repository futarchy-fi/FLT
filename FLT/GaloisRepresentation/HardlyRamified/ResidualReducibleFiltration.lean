/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CharacterFiltrationDeterminant
public import FLT.GaloisRepresentation.HardlyRamified.Defs

/-! # General reducible residual hardly ramified representations

Reducibility constructs an actual exact filtration by continuous characters.
Their product is the prescribed cyclotomic determinant. This retains the
extension and does not construct a characteristic-zero family.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified

/-- Every reducible residual HR representation has a cyclotomic-product filtration. -/
theorem exists_reducible_character_filtration
    {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
    {k V : Type*} [Field k] [Algebra ℤ_[p] k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    {hV : Module.rank k V = 2} {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified hpodd hV ρ) (hred : ¬ ρ.IsIrreducible) :
    ∃ F : GaloisRep.CharacterFiltration ρ,
      ∀ g : Field.absoluteGaloisGroup ℚ,
        F.χ₁ g 1 * F.χ₂ g 1 = algebraMap ℤ_[p] k
          (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv) := by
  have hdim := Module.finrank_eq_of_rank_eq hV
  obtain ⟨F⟩ := ρ.filtration_of_reducible hdim hred
  exact ⟨F, fun g ↦ (F.det_eq_product hdim g).symm.trans (hρ.det g)⟩

end GaloisRepresentation.IsHardlyRamified
