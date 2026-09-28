/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.CharacterInputs
public import FLT.Assembly.Inputs
public import FLT.Assembly.NormalizedReducibility
public import FLT.GaloisRepresentation.HardlyRamified.B5Inputs

/-!
# Three-adic traces from integral sorting and rank-one purity

Integral sorting supplies the invariant residual quotient for every lattice.
Ribet's lemma forces reducibility, and rank-one purity identifies a trivial
character. The trace descends through the normalized generic fibre.
-/

@[expose] public noncomputable section

open scoped TensorProduct ThreeAdicPlan
open GaloisRepresentation

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  [Algebra ℤ_[3] R] [Module.Free ℤ_[3] R] [Module.Finite ℤ_[3] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[3] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]

set_option maxHeartbeats 800000 in
-- The normalized tensor tower requires additional instance and equality reductions.
/-- Integral sorting and rank-one purity determine the trace over the original order. -/
theorem trace_eq_one_add_det_of_sorted_inputs
    (hsorted : SortedExtensionExists) (hpurity : ThreeAdicCharacterPurity)
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ) (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.trace R V (ρ g) = 1 + LinearMap.det (ρ g) := by
  obtain ⟨N⟩ := normalization_padic_order R
  obtain ⟨Λ, hΛ, _, _⟩ := exists_initial_stable_lattice
    (ρ.baseChange (NormalizedOrder R))
    (K := FractionRing R) Topology.IsInducing.subtypeVal
  have hdim : Module.rank (FractionRing R)
      (FractionRing R ⊗[NormalizedOrder R] (NormalizedOrder R ⊗[R] V)) = 2 := by
    rw [Module.rank_baseChange, Module.rank_baseChange, hV]
    simp
  have hr := hardlyRamified_of_stable_lattice hV hρ N Λ hΛ
  have ht := trace_eq_one_add_det_of_characterPurity hpurity
    ((ρ.baseChange (NormalizedOrder R)).baseChange (FractionRing R))
    Λ hΛ Topology.IsInducing.subtypeVal hdim hr
    (normalized_not_isIrreducible_of_sortedExtensionExists hsorted hV hρ) g
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_add, map_one]
  change LinearMap.trace (FractionRing R) _
      (((ρ g).baseChange (NormalizedOrder R)).baseChange (FractionRing R)) =
    1 + LinearMap.det (((ρ g).baseChange (NormalizedOrder R)).baseChange (FractionRing R)) at ht
  simpa only [LinearMap.trace_baseChange, LinearMap.det_baseChange,
    ← IsScalarTower.algebraMap_apply R (NormalizedOrder R) (FractionRing R)] using ht

/-- Sorting and rank-one purity give the Frobenius trace required by the compatible family. -/
theorem three_adic_of_sorted_inputs
    (hsorted : SortedExtensionExists) (hpurity : ThreeAdicCharacterPurity)
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (by decide : Odd 3) hV ρ)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    let v := hp.toHeightOneSpectrumRingOfIntegersRat
    (ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).trace R V = 1 + p := by
  let v := hp.toHeightOneSpectrumRingOfIntegersRat
  let g := Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ))
    (Field.AbsoluteGaloisGroup.adicArithFrob v)
  change LinearMap.trace R V (ρ g) = 1 + p
  rw [trace_eq_one_add_det_of_sorted_inputs hsorted hpurity hV hρ]
  change 1 + ρ.det g = 1 + p
  rw [hρ.det, B5Inputs.cyclotomicCharacter_adicArithFrob 3 p hp (by omega), map_natCast]

/-- Sorting and rank-one purity discharge the characteristic-zero trace input. -/
theorem threeAdicFrobeniusTrace_of_sorted_inputs
    (hsorted : SortedExtensionExists) (hpurity : ThreeAdicCharacterPurity) :
    FLT.Assembly.ThreeAdicFrobeniusTrace := by
  intro R _ _ _ _ _ _ _ _ _ V _ _ _ _ hV ρ hρ p hp hp5
  exact three_adic_of_sorted_inputs hsorted hpurity hV hρ p hp hp5

end ThreeAdicPlan
