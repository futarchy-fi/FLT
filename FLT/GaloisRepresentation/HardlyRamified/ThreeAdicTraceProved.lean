/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.PrimePowerSortingProof
public import FLT.Assembly.ThreeAdicTrace

/-!
# Three-adic traces over the original coefficient domain

Proved sorting supplies both inputs of the original-order trace theorem.
Trace equality does not assert that the original representation splits.
-/

@[expose] public noncomputable section

namespace GaloisRepresentation.IsHardlyRamified

variable {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

/-- Integral sorting determines the trace of every element over the original domain. -/
theorem trace_eq_one_add_det_three
    (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ)
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.trace R V (ρ g) = 1 + LinearMap.det (ρ g) :=
  ThreeAdicPlan.trace_eq_one_add_det_of_sorted_inputs
    (ThreeAdicPlan.sortedExtensionExists_of_primePowerSorting
      ThreeAdicPlan.primePowerSortedExtensionExists)
    ThreeAdicPlan.threeAdicCharacterPurity hV hρ g

/-- The original three-adic domain representation has the expected good Frobenius traces. -/
theorem three_adic_from_sorting
    (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    let v := hp.toHeightOneSpectrumRingOfIntegersRat
    (ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).trace R V = 1 + p :=
  ThreeAdicPlan.three_adic_of_sorted_inputs
    (ThreeAdicPlan.sortedExtensionExists_of_primePowerSorting
      ThreeAdicPlan.primePowerSortedExtensionExists)
    ThreeAdicPlan.threeAdicCharacterPurity hV hρ p hp hp5

end GaloisRepresentation.IsHardlyRamified
