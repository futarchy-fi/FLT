/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import FLT.NumberField.Completion.Finite
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Comparing the two local inertia definitions

The integral closure of the completed valuation ring is a valuation subring of
the algebraic closure. Ideal-theoretic local inertia lies in its residue-action kernel.
-/

@[expose] public section

open NumberField
open scoped Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv

/-- The integral closure of the completed valuation ring, viewed as a valuation subring. -/
noncomputable def localClosureValuation : ValuationSubring Ω :=
  ⟨(integralClosure O Ω).toSubring, fun x ↦ by
    obtain hx | hx := le_total (spectralNorm Kv Ω x) 1
    · exact Or.inl (isIntegral_of_spectralNorm_le_one hx)
    · apply Or.inr
      apply isIntegral_of_spectralNorm_le_one
      rw [spectralNorm_inv]
      exact inv_le_one_of_one_le₀ hx⟩

/-- The integral closure valuation restricts to the original completed valuation ring. -/
theorem localClosureValuation_comap :
    ((localClosureValuation v).comap (algebraMap Kv Ω)).toSubring =
    (algebraMap O Kv).range := by
  ext x
  change IsIntegral O (algebraMap Kv Ω x) ↔ ∃ y : O, algebraMap O Kv y = x
  rw [isIntegral_algebraMap_iff]
  exact IsIntegrallyClosed.isIntegral_iff

/-- Every local Galois automorphism preserves the integral closure valuation ring. -/
noncomputable def localClosureDecomposition (σ : Field.absoluteGaloisGroup Kv) :
    (localClosureValuation v).decompositionSubgroup Kv :=
  ⟨σ, by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy.map (σ.toAlgHom.restrictScalars O)
    · intro hx
      refine ⟨σ.symm x, hx.map (σ.symm.toAlgHom.restrictScalars O), ?_⟩
      exact σ.apply_symm_apply x⟩

/-- Ideal-theoretic local inertia acts trivially on the residue field of the valuation subring. -/
theorem localClosureDecomposition_mem_inertia (σ : Field.absoluteGaloisGroup Kv)
    (hσ : σ ∈ localInertiaGroup v) :
    localClosureDecomposition v σ ∈ (localClosureValuation v).inertiaSubgroup Kv := by
  change MulSemiringAction.toRingAut _ _ (localClosureDecomposition v σ) = 1
  apply RingEquiv.ext
  intro x
  obtain ⟨x,rfl⟩ := IsLocalRing.residue_surjective x
  change (localClosureDecomposition v σ) • IsLocalRing.residue _ x = IsLocalRing.residue _ x
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hσ x

open IsDedekindDomain.HeightOneSpectrum

set_option backward.isDefEq.respectTransparency false in
/-- A rational prime is a unit in the completed integer ring at every distinct prime. -/
theorem prime_isUnit_adicCompletionIntegers {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) :
    IsUnit (p : hℓ.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ) := by
  let v := hℓ.toHeightOneSpectrumRingOfIntegersRat
  apply adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr
  change Valued.v ((v.adicCompletionIntegers ℚ).subtype p) = 1
  rw [map_natCast, ← map_natCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)) p]
  have hv := v.valuedAdicCompletion_eq_valuation (K := ℚ) (p : 𝓞 ℚ)
  have hv' : Valued.v (p : v.adicCompletion ℚ) = v.valuation ℚ (p : ℚ) := by
    simpa using hv
  rw [map_natCast, hv']
  rw [← map_natCast (algebraMap (𝓞 ℚ) ℚ) p, valuation_eq_one_iff_notMem]
  change Rat.ringOfIntegersEquiv (p : 𝓞 ℚ) ∉ Ideal.span {(ℓ : ℤ)}
  rw [map_natCast, Ideal.mem_span_singleton, Int.ofNat_dvd]
  exact fun h ↦ hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)

open ValuativeRel

/-- The valuative relation induced by the completion's existing adic valuation. -/
@[instance_reducible]
noncomputable def completionValuativeRel : ValuativeRel Kv :=
  ValuativeRel.ofValuation (Valued.v (R := Kv))
attribute [local instance] completionValuativeRel
local instance : (Valued.v (R := Kv)).Compatible := Valuation.Compatible.ofValuation _
local instance : IsValuativeTopology Kv :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v (R := Kv))
    (fun {_} ↦ Valued.is_topological_valuation _)
local instance : ValuativeRel.IsNontrivial Kv :=
  (ValuativeRel.isNontrivial_iff_isNontrivial (Valued.v (R := Kv))).mpr inferInstance
/-- The adic completion is a nonarchimedean local field for its induced valuative relation. -/
theorem completion_isNonarchimedeanLocalField : IsNonarchimedeanLocalField Kv := ⟨⟩
/-- The canonical integer ring for this relation equals the original adic integer ring. -/
theorem completion_integerRing_eq :
    (𝒪[Kv] : Subring Kv) = (v.adicCompletionIntegers K).toSubring := by
  ext x
  change valuation Kv x ≤ 1 ↔ Valued.v x ≤ 1
  simpa only [map_one] using
    (ValuativeRel.isEquiv (valuation Kv) (Valued.v (R := Kv))) x 1

end NumberField
