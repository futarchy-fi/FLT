/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteTameQuotient
public import Mathlib.GroupTheory.Sylow

/-!
# Surjectivity of first ramification restriction

Finite inertia restriction is surjective by absolute inertia lifting. First
ramification is its normal Sylow p-subgroup, since the tame quotient has order
prime to p. Surjective homomorphisms preserve Sylow subgroups.
-/

@[expose] public section

open NumberField IsLocalRing
namespace LocalRamification

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Γ" => Field.absoluteGaloisGroup Kv

attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- The index-zero lower group is finite inertia. -/
noncomputable abbrev finiteInertia (N : OpenNormalSubgroup Γ) :=
  ramificationGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
    Gal(IntermediateField.fixedField N.1.1/Kv) 0

/-- First ramification, viewed as a subgroup of finite inertia. -/
noncomputable abbrev finiteFirstInertia (N : OpenNormalSubgroup Γ) :=
  (firstGroup (IntegralClosure O (IntermediateField.fixedField N.1.1))
    Gal(IntermediateField.fixedField N.1.1/Kv)).comap (finiteInertia v N).subtype

/-- Absolute inertia restricts into finite inertia. -/
theorem finiteRestriction_mem_inertia (N : OpenNormalSubgroup Γ)
    (σ : localInertiaGroup v) : finiteRestriction v N σ ∈ finiteInertia v N := by
  simp only [finiteInertia, ramificationGroup, Nat.zero_add, pow_one]
  rw [ ← map_localInertiaGroup_eq_finiteInertia v N]
  exact ⟨σ.1, σ.2, rfl⟩

/-- Every finite inertia element lifts to absolute inertia. -/
theorem finiteInertia_exists_lift (N : OpenNormalSubgroup Γ) (σ : finiteInertia v N) :
    ∃ τ : localInertiaGroup v, finiteRestriction v N τ = σ.1 := by
  have h := σ.2
  simp only [finiteInertia, ramificationGroup, Nat.zero_add, pow_one] at h
  rw [ ← map_localInertiaGroup_eq_finiteInertia v N] at h
  obtain ⟨τ, hτ, heq⟩ := h
  exact ⟨⟨τ, hτ⟩, heq⟩

/-- Restriction through a finite Galois tower preserves inertia. -/
theorem finiteTowerRestriction_mem_inertia {N M : OpenNormalSubgroup Γ} (h : N ≤ M)
    (σ : finiteInertia v N) : finiteTowerRestriction v h σ.1 ∈ finiteInertia v M := by
  obtain ⟨τ, hτ⟩ := finiteInertia_exists_lift v N σ
  rw [← hτ]
  change ((finiteTowerRestriction v h).comp (finiteRestriction v N)) τ ∈ _
  rw [finiteTowerRestriction_comp]
  exact finiteRestriction_mem_inertia v M τ

/-- Restriction between finite inertia groups. -/
noncomputable def finiteInertiaTowerRestriction {N M : OpenNormalSubgroup Γ} (h : N ≤ M) :
    finiteInertia v N →* finiteInertia v M :=
  ((finiteTowerRestriction v h).domRestrict _).codRestrict _
    (finiteTowerRestriction_mem_inertia v h)

/-- Finite inertia restriction is surjective. -/
theorem finiteInertiaTowerRestriction_surjective {N M : OpenNormalSubgroup Γ} (h : N ≤ M) :
    Function.Surjective (finiteInertiaTowerRestriction v h) := by
  intro σ
  obtain ⟨τ, hτ⟩ := finiteInertia_exists_lift v M σ
  refine ⟨⟨finiteRestriction v N τ, finiteRestriction_mem_inertia v N τ⟩, Subtype.ext ?_⟩
  exact (DFunLike.congr_fun (finiteTowerRestriction_comp v h) τ).trans hτ

/-- Finite first ramification is a p-subgroup of inertia. -/
theorem finiteFirstInertia_isPGroup (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
    (N : OpenNormalSubgroup Γ) : IsPGroup p (finiteFirstInertia v N) := by
  apply (finite_firstGroup_isPGroup v p N).of_equiv
    (Subgroup.subgroupOfEquivOfLe (H := firstGroup _ _) (K := finiteInertia v N) ?_).symm
  intro σ hσ
  simpa only [finiteInertia, ramificationGroup, Nat.zero_add, pow_one] using
    firstGroup_le_inertia _ _ hσ

/-- The tame quotient makes first ramification a Sylow subgroup of inertia. -/
noncomputable def finiteFirstSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
    (N : OpenNormalSubgroup Γ) : Sylow p (finiteInertia v N) :=
  (finiteFirstInertia_isPGroup v p N).toSylow (by
    rw [Subgroup.index_eq_card]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (finiteLevel_tame_card_coprime v N p).symm)

/-- First ramification restriction is surjective at every finite Galois tower. -/
theorem finiteFirstTowerRestriction_surjective
    {N M : OpenNormalSubgroup Γ} (h : N ≤ M) :
    Function.Surjective (finiteFirstTowerRestriction v h) := by
  let p := ringChar (ResidueField O)
  let : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField O) p⟩
  let P := finiteFirstSylow v p N
  let Q := P.mapSurjective (finiteInertiaTowerRestriction_surjective v h)
  have hle : finiteFirstInertia v M ≤ Q :=
    (finiteFirstInertia_isPGroup v p M).le_sylow_of_normal Q
  intro σ
  have hσ : σ.1 ∈ finiteInertia v M := by
    simpa only [finiteInertia, ramificationGroup, Nat.zero_add, pow_one] using
      firstGroup_le_inertia _ _ σ.2
  obtain ⟨τ, hτ, heq⟩ := hle (show (⟨σ.1, hσ⟩ : finiteInertia v M) ∈
    finiteFirstInertia v M from σ.2)
  refine ⟨⟨τ.1, hτ⟩, Subtype.ext ?_⟩
  change finiteTowerRestriction v h τ.1 = σ.1
  exact congrArg (fun x : finiteInertia v M ↦ x.1) heq

end LocalRamification
