/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteTameQuotient
public import FLT.LocalClassFieldTheory.ResidueGaloisEquiv
public import Mathlib.GroupTheory.Nilpotent

/-!
# Solvability of finite local Galois groups

First ramification is a finite p-group. The tame character embeds its
quotient in residue units, and the residue action has cyclic image.
These two extensions prove solvability of the actual Galois group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing LocalRamification

variable (S G : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Group G] [MulSemiringAction G S] [Finite G] [FaithfulSMul G S]
  [Finite (ResidueField S)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [Finite (ResidueField S)] in
include p in
/-- Wild inertia is solvable because the proved first ramification group is a p-group. -/
theorem localWildInertia_solvable : Group.IsSolvable (firstGroup S G) := by
  let := (firstGroup_isPGroup S G p).isNilpotent
  infer_instance

include p in
/-- The tame character and wild p-group prove solvability of finite inertia. -/
theorem localInertia_solvable : Group.IsSolvable (ramificationGroup S G 0) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let f := finiteTameCharacter S G hπ
  let j : f.ker →* firstGroup S G :=
    { toFun := fun σ => ⟨σ.val.val, by
        have h := σ.property
        simp only [f, finiteTameCharacter_ker, Subgroup.mem_comap] at h
        exact h⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let := localWildInertia_solvable S G p
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := j) (fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : firstGroup S G => z.val) h)
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

variable (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [IsLocalHom (algebraMap R S)]

include R S p in
/-- A finite Galois extension of DVR fraction fields with finite residue field
has solvable group. -/
theorem localGalois_solvable : Group.IsSolvable Gal(L/K) := by
  let := IsIntegralClosure.MulSemiringAction R K L S
  let : SMulDistribClass Gal(L/K) S L := ⟨fun g s x => by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    exact (algebraMap_galRestrictHom_apply R K L S g s).symm⟩
  let : Algebra.IsIntegral R S := ⟨IsIntegralClosure.isIntegral R L⟩
  let : IsGaloisGroup Gal(L/K) R S :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
  let : FaithfulSMul Gal(L/K) S := IsGaloisGroup.faithful R
  let := localInertia_solvable S Gal(L/K) p
  let : IsCyclic Gal(ResidueField S/ResidueField R) := inferInstance
  let : CommGroup Gal(ResidueField S/ResidueField R) := IsCyclic.commGroup
  apply Group.isSolvable_of_ker_le_range
    (ramificationGroup S Gal(L/K) 0).subtype (residueGaloisAction R S K L)
  intro g hg
  rw [Subgroup.range_subtype]
  intro x
  change g • x - x ∈ maximalIdeal S ^ (0 + 1)
  rw [pow_one, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact congrArg (fun σ : Gal(ResidueField S/ResidueField R) => σ (residue S x)) hg

end LocalClassFieldTheory
