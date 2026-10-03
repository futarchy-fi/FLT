/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteTameQuotient

/-!
# Commutativity of the absolute tame inertia quotient

Every finite tame character kills the difference of the two products.
The definition of wild inertia then puts this difference in wild inertia.
-/

@[expose] public noncomputable section
namespace LocalRamification
open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Γ" => Field.absoluteGaloisGroup Kv

attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

set_option maxHeartbeats 1000000 in
-- Finite integral-closure instances require an extended elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
/-- The actual absolute inertia quotient by wild inertia is commutative. -/
theorem tameInertia_commute (a b : localInertiaGroup v ⧸ wildInertia v) : Commute a b := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  change QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply (mem_wildInertia_iff v _).mpr
  intro N
  let D := IntegralClosure O (IntermediateField.fixedField N.1.1)
  let H := Gal(IntermediateField.fixedField N.1.1/Kv)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hin (σ : localInertiaGroup v) : finiteRestriction v N σ ∈ ramificationGroup D H 0 := by
    simp only [ramificationGroup, zero_add, pow_one]
    rw [← map_localInertiaGroup_eq_finiteInertia v N]
    exact ⟨σ.1, σ.2, rfl⟩
  let f : localInertiaGroup v →* ramificationGroup D H 0 :=
    (finiteRestriction v N).codRestrict _ hin
  have hk : f (a * b / (b * a)) ∈ (finiteTameCharacter D H hπ).ker := by
    let t := (finiteTameCharacter D H hπ).comp f
    change t (a * b / (b * a)) = 1
    rw [map_div, map_mul, map_mul, mul_comm (t a) (t b), div_self']
  rw [finiteTameCharacter_ker D H hπ] at hk
  exact hk

end LocalRamification
