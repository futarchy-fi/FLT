/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.DedekindDomain.AdicValuation

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Restriction of local inertia

Comparison of local absolute inertia with the inertia of finite subextensions.
-/

@[expose] public section

open NumberField

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "ᵐ" => IsLocalRing.maximalIdeal
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "ᵊaᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "Aᵥ" => IntegralClosure ᵊaᵥ (Kᵥᵃˡᵍ)

attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring

/-- The map on integral closures induced by an algebra homomorphism. -/
noncomputable def IntegralClosure.map
    {R E L : Type*} [CommRing R] [CommRing E] [CommRing L]
    [Algebra R E] [Algebra R L] (f : E →ₐ[R] L) :
    IntegralClosure R E →+* IntegralClosure R L where
  toFun x := ⟨f x.1, x.2.map f⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)

/-- An injective algebra homomorphism induces an injective map on integral closures. -/
lemma IntegralClosure.map_injective
    {R E L : Type*} [CommRing R] [CommRing E] [CommRing L]
    [Algebra R E] [Algebra R L] (f : E →ₐ[R] L) (hf : Function.Injective f) :
    Function.Injective (IntegralClosure.map f) := by
  intro x y h
  apply Subtype.ext
  exact hf (congrArg Subtype.val h)

set_option maxHeartbeats 1000000 in
-- The profinite Galois-action and residue-field instances require extended elaboration time.
set_option synthInstance.maxHeartbeats 100000 in
set_option linter.style.haveILetI false in
/-- Restriction of local absolute inertia to a finite Galois fixed field is its ideal inertia. -/
lemma map_localInertiaGroup_eq_finiteInertia
    (N : OpenNormalSubgroup (Γ Kᵥ)) :
    Subgroup.map
        (AlgEquiv.restrictNormalHom
          (IntermediateField.fixedField N.1.1 : IntermediateField Kᵥ (Kᵥᵃˡᵍ)))
        (localInertiaGroup v) =
      (IsLocalRing.maximalIdeal
        (IntegralClosure 𝒪ᵥ (IntermediateField.fixedField N.1.1))).inertia
        Gal(IntermediateField.fixedField N.1.1/Kᵥ) := by
  let L : IntermediateField Kᵥ (Kᵥᵃˡᵍ) := IntermediateField.fixedField N.1.1
  let B := IntegralClosure 𝒪ᵥ L
  let A := IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)
  let P := IsLocalRing.maximalIdeal B
  let M := IsLocalRing.maximalIdeal A
  let C : ClosedSubgroup (Γ Kᵥ) := ⟨N.1.1, N.toOpenSubgroup.isClosed⟩
  letI : FiniteDimensional Kᵥ L := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup (Γ Kᵥ))]
    exact N.isOpen'
  letI : IsGalois Kᵥ L := by
    rw [← InfiniteGalois.normal_iff_isGalois]
    rw [InfiniteGalois.fixingSubgroup_fixedField
      (⟨N.1.1, N.toOpenSubgroup.isClosed⟩ : ClosedSubgroup (Γ Kᵥ))]
    infer_instance
  let i : L →ₐ[𝒪ᵥ] (Kᵥᵃˡᵍ) := L.val.restrictScalars 𝒪ᵥ
  letI : Algebra B A := (IntegralClosure.map i).toAlgebra
  letI : IsScalarTower 𝒪ᵥ B A := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    rfl
  letI : Algebra B (Kᵥᵃˡᵍ) :=
    (i.toRingHom.comp (algebraMap B L)).toAlgebra
  letI : IsScalarTower B L (Kᵥᵃˡᵍ) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B A (Kᵥᵃˡᵍ) := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    rfl
  letI : Algebra.IsIntegral B A := ⟨fun x ↦
    (Algebra.IsIntegral.isIntegral (R := 𝒪ᵥ) x).tower_top⟩
  letI : FaithfulSMul B A := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact IntegralClosure.map_injective i i.injective
  letI : IsFractionRing B L := by
    dsimp only [B]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_finite_extension Kᵥ L
  letI : IsFractionRing A (Kᵥᵃˡᵍ) := by
    letI : Algebra.IsAlgebraic 𝒪ᵥ (Kᵥᵃˡᵍ) :=
      (IsFractionRing.comap_isAlgebraic_iff
        (A := 𝒪ᵥ) (K := Kᵥ) (C := Kᵥᵃˡᵍ)).mpr
        (inferInstance : Algebra.IsAlgebraic Kᵥ (Kᵥᵃˡᵍ))
    dsimp only [A]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_algebraic fun x hx ↦ by
      apply Subtype.ext
      apply (algebraMap Kᵥ (Kᵥᵃˡᵍ)).injective
      have hx' := hx
      change (algebraMap Kᵥ (Kᵥᵃˡᵍ)) (x : Kᵥ) = 0 at hx'
      exact hx'.trans (map_zero (algebraMap Kᵥ (Kᵥᵃˡᵍ))).symm
  letI : CompactSpace C.toSubgroup :=
    isCompact_iff_compactSpace.mp C.isClosed'.isCompact
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : SMulDistribClass C.toSubgroup A (Kᵥᵃˡᵍ) := ⟨fun g a x ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  haveI : IsGaloisGroup C.toSubgroup L (Kᵥᵃˡᵍ) := by
    exact IsGaloisGroup.subgroup (Γ Kᵥ) Kᵥ (Kᵥᵃˡᵍ) N.1.1
  letI : IsGaloisGroup C.toSubgroup B A :=
    IsGaloisGroup.of_isFractionRing C.toSubgroup B A L (Kᵥᵃˡᵍ)
  letI : ContinuousSMul C.toSubgroup A := by infer_instance
  letI : M.LiesOver P := by dsimp only [M, P]; infer_instance
  change Subgroup.map (AlgEquiv.restrictNormalHom L) (localInertiaGroup v) =
    P.inertia Gal(L/Kᵥ)
  apply le_antisymm
  · rintro τ ⟨σ, hσ, rfl⟩
    rw [AddSubgroup.mem_inertia]
    intro b
    change (AlgEquiv.restrictNormalHom L σ) • b - b ∈ P
    rw [Ideal.mem_of_liesOver M P]
    rw [map_sub]
    have hcompat : algebraMap B A ((AlgEquiv.restrictNormalHom L σ) • b) =
        σ • (algebraMap B A b) := by
      apply Subtype.ext
      exact AlgEquiv.restrictNormalHom_apply L σ b.1
    rw [hcompat]
    exact hσ (algebraMap B A b)
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (Kᵥᵃˡᵍ) τ
    let eA : A ≃ₐ[𝒪ᵥ] A := MulSemiringAction.toAlgEquiv 𝒪ᵥ A σ
    have hmapM : M = M.map eA :=
      (IsLocalRing.map_ringEquiv_maximalIdeal eA.toRingEquiv).symm
    let eRes : (A ⧸ M) ≃ₐ[B ⧸ P] (A ⧸ M) := {
      __ := Ideal.quotientEquiv M M eA.toRingEquiv hmapM
      commutes' := by
        rintro ⟨b⟩
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        change eA (algebraMap B A b) - algebraMap B A b ∈ M
        have hb : algebraMap B A (τ • b) - algebraMap B A b ∈ M := by
          rw [← map_sub, ← Ideal.mem_of_liesOver M P]
          exact hτ b
        have hcompat : eA (algebraMap B A b) = algebraMap B A (τ • b) := by
          apply Subtype.ext
          change σ ((algebraMap L (Kᵥᵃˡᵍ)) b.1) =
            (algebraMap L (Kᵥᵃˡᵍ)) (τ b.1)
          rw [← hσ]
          exact (AlgEquiv.restrictNormal_commutes σ L b.1).symm
        rwa [hcompat] }
    obtain ⟨n, hn⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := C.toSubgroup) P M eRes.symm
    refine ⟨n.1.1 * σ, ?_, ?_⟩
    · change ∀ a : A, (n.1.1 * σ) • a - a ∈ M
      intro a
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      have heA : eRes (Ideal.Quotient.mk M a) =
          Ideal.Quotient.mk M (σ • a) := rfl
      calc
        Ideal.Quotient.mk M ((n.1.1 * σ) • a) =
            Ideal.Quotient.stabilizerHom M P C.toSubgroup n
              (Ideal.Quotient.mk M (σ • a)) := by rw [mul_smul]; rfl
        _ = eRes.symm (Ideal.Quotient.mk M (σ • a)) := by rw [hn]
        _ = eRes.symm (eRes (Ideal.Quotient.mk M a)) := by rw [heA]
        _ = Ideal.Quotient.mk M a := eRes.symm_apply_apply _
    · have hnres : AlgEquiv.restrictNormalHom L n.1.1 = 1 := by
        apply AlgEquiv.ext
        intro x
        apply Subtype.ext
        exact (AlgEquiv.restrictNormal_commutes n.1.1 L x).trans
          (x.2 ⟨n.1.1, n.1.2⟩)
      rw [map_mul, hnres, hσ, one_mul]

