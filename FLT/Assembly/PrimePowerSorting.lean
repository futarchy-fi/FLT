/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.CharacterGlobalModel
public import FLT.Assembly.CharacterInputs
public import FLT.GaloisRepresentation.HardlyRamified.ModThreeSorted
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Character purity from integral sorting at every three-power level

Full category-D sorting supplies the actual finite quotient models of an
integral character. Scalar complex conjugation and separatedness then determine
the character. The residual sorting statement is a direct specialization.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every three-primary category-D object admits an integral sorted extension. -/
def PrimePowerSortedExtensionExists : Prop :=
  ∀ (H : FiniteFlatObject ZInvTwo), InCategoryD H →
    Nonempty (SortedFiniteFlatExtension H)

/-- Sorting all category-D objects includes the objects killed by three. -/
theorem sortedExtensionExists_of_primePowerSorting
    (hsorted : PrimePowerSortedExtensionExists) : SortedExtensionExists :=
  fun H hH _ ↦ hsorted H hH

/-- Sorting at every finite coefficient level determines integral three-adic characters. -/
theorem threeAdicCharacterPurity_of_primePowerSorting
    (hsorted : PrimePowerSortedExtensionExists) : ThreeAdicCharacterPurity := by
  intro O instRing instDomain instDVR instAlgebra instFinite instFree
    instTopology instTopRing instModuleTopology ψ hc hf hu
  let instCompact : CompactSpace O := Module.Finite.compactSpace ℤ_[3] O
  let instT2 : T2Space O := IsModuleTopology.t2Space ℤ_[3]
  have hthree : (3 : O) ∈ IsLocalRing.maximalIdeal O := by
    change ¬ IsUnit (3 : O)
    rw [← map_ofNat (algebraMap ℤ_[3] O), isUnit_map_iff]
    rw [PadicInt.not_isUnit_iff]
    change ‖((3 : ℕ) : ℤ_[3])‖ < 1
    rw [PadicInt.norm_p]
    norm_num
  apply character_eq_one_or_cyclotomic_of_sorted_models
    (IsLocalRing.maximalIdeal O) hthree ψ
  intro n
  let I := IsLocalRing.maximalIdeal O ^ n
  have hI : IsOpen (I : Set O) := IsLocalRing.isOpen_maximalIdeal_pow O n
  let instFiniteQuotient : Finite (O ⧸ I) := IsLocalRing.isOpen_iff_finite_quotient.mp hI
  obtain ⟨M⟩ := characterQuotient_globalModel_of_flat_unramified ψ hc hf hu I hI n
    (Ideal.pow_mem_pow hthree n)
  let H := FiniteFlatObject.ofModel M.toModelOverZInvTwo
  let instHModule : Module ℤ_[3] H.points := inferInstanceAs (Module ℤ_[3] (O ⧸ I))
  obtain ⟨S⟩ := hsorted H M.inCategoryD
  let e : H.points ≃ₗ[ℤ_[3]] (O ⧸ I) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨H, instHModule, S, e, fun _ _ ↦ rfl⟩

end ThreeAdicPlan
