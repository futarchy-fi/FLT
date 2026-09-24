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

Comparison of local absolute inertia with the inertia of finite local subextensions.
We also construct the induced global prime, prove that it lies over the original
place, and show that local inertia restricts into its global inertia group.
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


namespace NumberField.InertiaComparison

variable (L : IntermediateField K (AlgebraicClosure K))

/-- Embed global integers into the integral closure of the completed valuation ring,
using the chosen embedding of algebraic closures. -/
noncomputable def localIntegersMap : (𝓞 L) →+* Aᵥ where
  toFun x := ⟨AlgebraicClosure.map (algebraMap K Kᵥ) (L.val x.1),
    by
      let : Algebra ℤ (AlgebraicClosure Kᵥ) := Ring.toIntAlgebra _
      have hx : IsIntegral ℤ
          (AlgebraicClosure.map (algebraMap K Kᵥ) (L.val x.1)) :=
        map_isIntegral_int
          ((AlgebraicClosure.map (algebraMap K Kᵥ)).comp L.val.toRingHom) x.2
      exact hx.tower_top (A := 𝒪ᵥ)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- The global prime obtained by pulling back the local maximal ideal. -/
noncomputable def localInducedPrime : Ideal (𝓞 L) :=
  (IsLocalRing.maximalIdeal Aᵥ).comap (localIntegersMap v L)

/-- The prime induced by the local algebraic closure is prime. -/
instance localInducedPrime_isPrime : (localInducedPrime v L).IsPrime := Ideal.comap_isPrime _ _

variable [Normal K L]
/-- Restrict local absolute Galois automorphisms to a normal global subextension. -/
noncomputable def localRestriction : Field.absoluteGaloisGroup Kᵥ →* Gal(L/K) :=
  (AlgEquiv.restrictNormalHom L).comp
    (Field.absoluteGaloisGroup.map (algebraMap K Kᵥ)).toMonoidHom

/-- The embedding of global integers intertwines local and global Galois actions. -/
lemma localIntegersMap_equivariant (σ : Field.absoluteGaloisGroup Kᵥ) (x : 𝓞 L) :
    localIntegersMap v L (localRestriction v L σ • x) = σ • localIntegersMap v L x := by
  apply Subtype.ext
  change AlgebraicClosure.map (algebraMap K Kᵥ)
    (L.val ((AlgEquiv.restrictNormalHom L
      (Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) σ)) x.1)) = _
  exact (congrArg (AlgebraicClosure.map (algebraMap K Kᵥ))
    (AlgEquiv.restrictNormalHom_apply L
      (Field.absoluteGaloisGroup.map (algebraMap K Kᵥ) σ) x.1)).trans
        (Field.absoluteGaloisGroup.lift_map _ _ _)

/-- Local inertia restricts into the inertia of the induced global prime. -/
lemma map_localInertiaGroup_le_globalInertia :
    (localInertiaGroup v).map (localRestriction v L) ≤
      (localInducedPrime v L).inertia Gal(L/K) := by
  rintro _ ⟨σ, hσ, rfl⟩ x
  change localIntegersMap v L (localRestriction v L σ • x - x) ∈
    IsLocalRing.maximalIdeal Aᵥ
  rw [map_sub, localIntegersMap_equivariant]
  exact hσ (localIntegersMap v L x)

omit [Normal K L] in
/-- On base-field integers the chosen embedding agrees with the completion map. -/
lemma localIntegersMap_algebraMap (x : 𝓞 K) :
    localIntegersMap v L (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap 𝒪ᵥ Aᵥ (algebraMap (𝓞 K) 𝒪ᵥ x) := by
  apply Subtype.ext
  change AlgebraicClosure.map (algebraMap K Kᵥ)
    (algebraMap K (AlgebraicClosure K) x.1) = _
  exact AlgebraicClosure.map_algebraMap _ _

/-- The induced global prime lies over the original finite place. -/
instance localInducedPrime_liesOver : (localInducedPrime v L).LiesOver v.asIdeal where
  over := by
    ext x
    change x ∈ v.asIdeal ↔
      localIntegersMap v L (algebraMap (𝓞 K) (𝓞 L) x) ∈ IsLocalRing.maximalIdeal Aᵥ
    rw [localIntegersMap_algebraMap]
    exact (Ideal.mem_of_liesOver (v.completionIdeal K) v.asIdeal x).trans
      (Ideal.mem_of_liesOver (IsLocalRing.maximalIdeal Aᵥ)
        (v.completionIdeal K) _)

omit [Normal K L] in
/-- The induced global prime is nonzero. -/
lemma localInducedPrime_ne_bot : localInducedPrime v L ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _

end NumberField.InertiaComparison
