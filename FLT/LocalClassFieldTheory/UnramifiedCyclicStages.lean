/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStageFrobenius
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Instances.ZMod

/-!
# Cyclic coordinates normalized by arithmetic Frobenius

The degree-n Galois group is identified with Z/n using the actual Frobenius
as generator. Composing inverse coordinates with restriction gives continuous
characters of the unramified union, normalized to take Frobenius to one.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "E[" n "]" => unramifiedFiniteStage R K C n

/-- The finite stage inside the union has its prescribed positive degree. -/
theorem finrank_unramifiedFiniteStage (n : UnramifiedIndex) :
    Module.finrank K (E[n]) = n.degree := by
  let e := IntermediateField.restrictAlgEquiv
    (unramifiedStage_le_maximalUnramified R K C n.degree)
  let := (unramifiedStage_isUnramified R K C n.degree).1
  exact e.toLinearEquiv.finrank_eq.symm.trans (finrank_unramifiedStage R K C n.degree)

/-- Arithmetic Frobenius generates the entire finite-stage Galois group. -/
theorem unramifiedStageFrobenius_mem_zpowers (n : UnramifiedIndex) (σ : Gal(E[n]/K)) :
    σ ∈ Subgroup.zpowers (unramifiedStageFrobenius R K C n) := by
  let S := integralClosure R (E[n])
  let h := unramifiedFiniteStage_isUnramified R K C n
  let : IsDiscreteValuationRing S := h.canonical_dvr
  let : Algebra.FormallyUnramified R S := h.canonical_unramified
  let : IsFractionRing S (E[n]) := integralClosure.isFractionRing_of_finite_extension K (E[n])
  let : IsLocalHom (algebraMap R S) := stageLocalHom R K C n
  obtain ⟨i, hi⟩ := arithmeticFrobenius_pow_surjective R S K (E[n]) σ
  exact ⟨(i.val : ℤ), by simpa only [zpow_natCast, unramifiedStageFrobenius] using hi⟩

/-- The cyclic coordinate sends one to arithmetic Frobenius. -/
def unramifiedStageCyclicEquiv (n : UnramifiedIndex) :
    Multiplicative (ZMod n.degree) ≃* Gal(E[n]/K) :=
  zmodMulEquivOfGenerator (unramifiedStageFrobenius_mem_zpowers R K C n)
    ((IsGalois.card_aut_eq_finrank K (E[n])).trans (finrank_unramifiedFiniteStage R K C n))

/-- Inverse cyclic coordinates are normalized at the chosen arithmetic generator. -/
theorem unramifiedStageCyclicEquiv_frobenius (n : UnramifiedIndex) :
    (unramifiedStageCyclicEquiv R K C n).symm (unramifiedStageFrobenius R K C n) =
      Multiplicative.ofAdd 1 :=
  zmodMulEquivOfGenerator_symm_apply_generator _ _

/-- A continuous degree-n unramified character on the Galois group of the union. -/
def unramifiedDegreeCharacter (n : UnramifiedIndex) :
    Gal(maximalUnramified R K C/K) →ₜ* Multiplicative (ZMod n.degree) where
  toMonoidHom := (unramifiedStageCyclicEquiv R K C n).symm.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (E[n]))
  continuous_toFun :=
    (show Continuous (unramifiedStageCyclicEquiv R K C n).symm from
      continuous_of_discreteTopology).comp
        (InfiniteGalois.restrictNormalHom_continuous (E[n]).toIntermediateField)

/-- Each degree character takes arithmetic Frobenius to one in Z/n. -/
theorem unramifiedDegreeCharacter_frobenius (n : UnramifiedIndex) :
    unramifiedDegreeCharacter R K C n (unramifiedFrobenius R K C) =
      Multiplicative.ofAdd 1 := by
  change (unramifiedStageCyclicEquiv R K C n).symm
    ((unramifiedFrobenius R K C).restrictNormal (E[n])) = _
  rw [unramifiedFrobenius_restrict, unramifiedStageCyclicEquiv_frobenius]

end LocalClassFieldTheory
