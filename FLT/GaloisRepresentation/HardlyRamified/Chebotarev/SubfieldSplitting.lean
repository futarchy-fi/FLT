/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Frobenius membership and splitting in fixed fields

Leaf H2 of `docs/CHEBOTAREV_PLAN.md`, with its cyclic-extension statement unchanged.
The stronger `frob_mem_iff_split_fixedField_of_normal` only requires the subgroup
to be normal. Unramifiedness descends to the fixed field, and restricting
Frobenius preserves the residue congruence. B1 identifies its order with the
residue degree, so triviality agrees with that of the independently chosen
Frobenius downstairs. The kernel of restriction is the original subgroup.
-/

@[expose] public section

open NumberField

namespace GaloisRepresentation.Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- Unramifiedness descends to an intermediate number field. -/
theorem unram_intermediateField (E : IntermediateField K L) (v : Prime K)
    (hu : Unram K L v) : Unram K E v := by
  intro p hp hpv
  let := hp
  let := hpv
  let : p.IsMaximal := hp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot p)
  obtain ⟨P, hP, hPp⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p
  let := hP
  let := hPp
  let : P.LiesOver v.asIdeal := Ideal.LiesOver.trans P p v.asIdeal
  let : Algebra.IsUnramifiedAt (𝓞 K) P := hu P hP.isPrime inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) p P

variable [IsGalois K L]

/-- The unramified primes whose chosen Frobenius is trivial. -/
def Split : Set (Prime K) := {v | Unram K L v ∧ frob K L v = 1}

/-- Restricting Frobenius to a normal intermediate field preserves its residue congruence. -/
theorem isArithFrobAt_restrictNormal (E : IntermediateField K L) [IsGalois K E]
    (w : Prime L) (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom E σ)
      (w.asIdeal.under (𝓞 E)) := by
  intro x
  change algebraMap (𝓞 E) (𝓞 L) _ ∈ w.asIdeal
  rw [map_sub, map_pow, Ideal.under_under]
  have hcomm : algebraMap (𝓞 E) (𝓞 L) ((AlgEquiv.restrictNormalHom E σ) • x) =
      σ • algebraMap (𝓞 E) (𝓞 L) x := by
    apply RingOfIntegers.ext
    exact AlgEquiv.restrictNormal_commutes σ E x
  change algebraMap (𝓞 E) (𝓞 L) ((AlgEquiv.restrictNormalHom E σ) • x) - _ ∈ _
  rw [hcomm]
  exact hσ (algebraMap (𝓞 E) (𝓞 L) x)

/-- Triviality of a restricted Frobenius is independent of the prime chosen downstairs. -/
theorem restrictNormal_frob_eq_one_iff (E : IntermediateField K L) [IsGalois K E]
    (v : Prime K) (hu : Unram K L v) :
    AlgEquiv.restrictNormalHom E (frob K L v) = 1 ↔ frob K E v = 1 := by
  let w := primeAbove K L v
  let u : Prime E := w.under (𝓞 E)
  have huv : u.asIdeal.under (𝓞 K) = v.asIdeal := by
    change (w.asIdeal.under (𝓞 E)).under (𝓞 K) = v.asIdeal
    rw [Ideal.under_under]
    exact primeAbove_under K L v
  have huE := unram_intermediateField K L E v hu
  let : u.asIdeal.LiesOver v.asIdeal := ⟨huv.symm⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) u.asIdeal := huE _ inferInstance inferInstance
  have hr := orderOf_eq_inertiaDeg_of_isArithFrobAt K E u
    (AlgEquiv.restrictNormalHom E (frob K L v))
    (isArithFrobAt_restrictNormal K L E w _ (isArithFrobAt_frob K L v))
  have hf := orderOf_frob_eq_inertiaDeg K E v u huv huE
  exact orderOf_eq_one_iff.symm.trans ((hr.trans hf.symm).congr_left.trans orderOf_eq_one_iff)

/-- A Frobenius belongs to a normal subgroup exactly when the base prime splits in
its fixed field. Unramifiedness in the top field is retained as a hypothesis. -/
theorem frob_mem_iff_split_fixedField_of_normal (D : Subgroup Gal(L/K)) [D.Normal]
    (v : Prime K) (hu : Unram K L v) :
    frob K L v ∈ D ↔ v ∈ Split K (IntermediateField.fixedField D) := by
  have hker : (AlgEquiv.restrictNormalHom (IntermediateField.fixedField D)).ker = D := by
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  conv_lhs => rw [← hker, MonoidHom.mem_ker]
  rw [restrictNormal_frob_eq_one_iff K L _ v hu]
  exact (and_iff_right (unram_intermediateField K L _ v hu)).symm

/-- In a cyclic extension, subgroup membership of Frobenius detects splitting in
the fixed field (leaf H2). -/
theorem frob_mem_iff_split_fixedField [IsCyclic Gal(L/K)] (D : Subgroup Gal(L/K))
    (v : Prime K) (hu : Unram K L v) :
    frob K L v ∈ D ↔ v ∈ Split K (IntermediateField.fixedField D) :=
  frob_mem_iff_split_fixedField_of_normal K L D v hu

end GaloisRepresentation.Chebotarev
