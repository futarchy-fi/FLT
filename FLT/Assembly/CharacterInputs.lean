/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.TraceLinearAlgebra
public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero

/-!
# The rank-one input to the three-adic trace calculation

The remaining character classification concerns continuous integral characters
unramified outside three and finite flat at every open coefficient level.
Once it is supplied, the integral characters of a reducible hardly ramified
representation give the trace identity.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Integral characters finite flat at three and unramified elsewhere are trivial or cyclotomic. -/
def ThreeAdicCharacterPurity : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[3] O] [Module.Finite ℤ_[3] O] [Module.Free ℤ_[3] O]
    [TopologicalSpace O] [IsTopologicalRing O] [IsModuleTopology ℤ_[3] O]
    (ψ : Field.absoluteGaloisGroup ℚ →* Oˣ),
    Continuous ψ → Flat3 ψ → UnramifiedOutsideThree ψ →
      ψ = 1 ∨ ψ = threeAdicCyclotomic

/-- Rank-one purity determines the trace of a reducible hardly ramified lattice. -/
theorem trace_eq_one_add_det_of_characterPurity
    (hpurity : ThreeAdicCharacterPurity)
    {O K W : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
    [TopologicalSpace O] [IsTopologicalRing O]
    [TopologicalSpace K] [IsTopologicalRing K] [Algebra ℤ_[3] O]
    [Module.Finite ℤ_[3] O] [Module.Free ℤ_[3] O] [IsModuleTopology ℤ_[3] O]
    [FiniteDimensional K W]
    (ρK : GaloisRep ℚ K W)
    (Λ : Submodule O W) (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K)) (hdim : Module.rank K W = 2)
    (hρΛ : let _instLattice := hΛ.isLattice
      GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide)
        ((Submodule.IsLattice.rank' K Λ).trans hdim) (latticeGaloisRep ρK Λ hΛ hOK))
    (hred : ¬ ρK.IsIrreducible) (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.trace K W (ρK g) = 1 + LinearMap.det (ρK g) := by
  obtain ⟨ψ₁, ψ₂, hc₁, _, hf₁, _, hu₁, _, hext, hproduct⟩ :=
    integral_characters_of_reducible ρK Λ hΛ hOK hdim hρΛ hred
  have htrivial : ψ₁ = 1 ∨ ψ₂ = 1 := by
    rcases hpurity ψ₁ hc₁ hf₁ hu₁ with h | h
    · exact Or.inl h
    · right
      rw [h] at hproduct
      exact mul_left_cancel (hproduct.trans (mul_one _).symm)
  apply hext.1.trace_eq_one_add_det_of_trivial_character
    (Module.finrank_eq_of_rank_eq hdim) _ g
  rcases htrivial with h | h
  · left
    simp [h]
  · right
    simp [h]

end ThreeAdicPlan
