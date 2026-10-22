/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFirstOrderLocalRigidity
public import FLT.Mazur.ScalarDifferentialPrincipalRigidity

/-!
# Original source stalk rigidity from first-order scalar generation

At a source prime, a separable residue extension and scalar generation of the
maximal ideal modulo its square imply full stalk rigidity. Finiteness is used
only for that maximal ideal and for spreading differentials. No reducedness,
scalar Noetherianity, or finite type of the full stalk is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFirstOrderStalkRigidity
open IsLocalRing
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.EssFiniteType R A] (Q : PrimeSpectrum A)
/-- The scalar localization acts on the full source stalk through the canonical local map. -/
local instance firstOrderStalkAlgebra :
    Algebra (Localization.AtPrime (Q.asIdeal.under R)) (Localization.AtPrime Q.asIdeal) :=
  Localization.AtPrime.algebraOfLiesOver (Q.asIdeal.under R) Q.asIdeal
variable [Algebra.IsSeparable (Q.asIdeal.under R).ResidueField Q.asIdeal.ResidueField]
set_option quotPrecheck false
local notation "L" => Localization.AtPrime Q.asIdeal
local notation "m" => maximalIdeal L
local notation "J" => (Q.asIdeal.under R).map (algebraMap R L)

/-- First-order scalar generation at the exact source prime kills all stalk differentials. -/
theorem isUnramifiedAt (hfg : (m).FG) (h : m ≤ J ⊔ m ^ 2) :
    Algebra.IsUnramifiedAt R Q.asIdeal := by
  apply (Algebra.isUnramifiedAt_iff_map_eq R (Q.asIdeal.under R) Q.asIdeal).mpr
  refine ⟨inferInstance, ScalarFirstOrderLocalRigidity.ideal_eq_maximal J ?_ hfg h⟩
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change algebraMap R L r ∈ m
  rw [IsScalarTower.algebraMap_apply R A L]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q.asIdeal _).mpr hr

/-- Full stalk rigidity spreads to an original differential annihilator away from the prime. -/
theorem exists_annihilator (hfg : (m).FG) (h : m ≤ J ⊔ m ^ 2) :
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), a ∉ Q.asIdeal := by
  have hu : Q ∈ Algebra.unramifiedLocus R A := isUnramifiedAt Q hfg h
  rw [Algebra.unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus] at hu
  exact Set.not_subset.mp hu

/-- The first-order criterion constructs an actual principal neighborhood in the full source. -/
theorem exists_principal (hfg : (m).FG) (h : m ≤ J ⊔ m ^ 2) :
    ∃ a : A, a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  obtain ⟨a, ha, hQa⟩ := exists_annihilator Q hfg h
  exact ⟨a, hQa, ScalarDifferentialPrincipalRigidity.away_formallyUnramified a ha⟩

/-- Source Noetherianity supplies the finite maximal ideal without any scalar-ring finiteness. -/
theorem exists_principal_of_noetherian [IsNoetherianRing A] (h : m ≤ J ⊔ m ^ 2) :
    ∃ a : A, a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) :=
  exists_principal Q (IsNoetherian.noetherian _) h

end FLT.Mazur.ScalarFirstOrderStalkRigidity
