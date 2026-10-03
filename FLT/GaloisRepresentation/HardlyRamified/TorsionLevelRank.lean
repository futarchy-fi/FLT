/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionModelComparisons
public import FLT.Deformations.RepresentationTheory.PadicPowerCardinality
public import FLT.GroupScheme.RaynaudAugmentationRank

/-!
# Height of the actual hardly ramified integral levels

The integral rank is computed from the original coefficient module, through
the selected equivariant point comparison. It is not an additional hypothesis.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan PrimePower

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

/-- The height is twice the original coefficient degree over the p-adic integers. -/
abbrev torsionHeight := Module.finrank ℤ_[p] R * 2

/-- The actual level's generic point count has the required height growth. -/
theorem torsionModel_card (n : ℕ) :
    Nat.card (hρ.torsionModel n).Points = p ^ (n * torsionHeight (p := p) (R := R)) := by
  rw [Nat.card_congr (hρ.torsionPoints n).toEquiv]
  change Nat.card (Level (V := V) (p : R) n) = _
  rw [card_level, Module.finrank_eq_of_rank_eq hV]

/-- Finite flatness identifies this count with the integral coordinate rank. -/
theorem torsionModel_finrank (n : ℕ) :
    Module.finrank ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (hρ.torsionModel n).CoordinateRing = p ^ (n * torsionHeight (p := p) (R := R)) := by
  rw [FF.coordinate_finrank, hρ.torsionModel_card]

/-- Level zero is the trivial group on generic points. -/
theorem torsionModel_card_zero : Nat.card (hρ.torsionModel 0).Points = 1 := by
  rw [hρ.torsionModel_card, Nat.zero_mul, pow_zero]

omit [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R] in
/-- The tower is nonzero: its height is positive. -/
theorem torsionHeight_pos : 0 < torsionHeight (p := p) (R := R) :=
  Nat.mul_pos (Module.finrank_pos (R := ℤ_[p]) (M := R)) (by decide)

end GaloisRepresentation.IsHardlyRamified
