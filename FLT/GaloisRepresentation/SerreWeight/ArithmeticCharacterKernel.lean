/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaCyclicQuotient
public import FLT.AbsoluteGaloisGroup.LocalCyclotomicTame
public import FLT.GaloisRepresentation.SerreWeight.CyclicPairKernel
public import FLT.GaloisRepresentation.SerreWeight.LocalCharacterNormalization

/-!
# Arithmetic kernel gates for character normalization

The cyclotomic kernel is the specified tame-abelian inertia subgroup.
For prime-field characters, an open kernel alone suffices: the joint finite
inertia image is cyclic of prime-to-p order. No numerical weight is inferred.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.SerreWeight
variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "I" => localInertiaGroup v
local notation "G" => Field.absoluteGaloisGroup
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)

/-- The independent arithmetic cyclotomic kernel is the specified tame subgroup. -/
theorem inertiaCyclotomic_ker_eq_tame :
    (LocalCyclotomic.inertiaCharacter p).ker =
      (localTameAbelianInertiaGroup v).subgroupOf I := by
  rw [localTameAbelianInertiaGroup_subgroupOf_eq_tameCharacter_ker,
    ← LocalCyclotomic.tameCharacter_eq_inertiaCharacter]
  ext g
  change Units.mapEquiv (LocalCyclotomic.residueEquiv p).toMulEquiv
    (tameCharacter v g) = 1 ↔ tameCharacter v g = 1
  exact (Units.mapEquiv (LocalCyclotomic.residueEquiv p).toMulEquiv).map_eq_one_iff

/-- Tameness on the original local group supplies the kernel premise for normalization. -/
theorem inertiaCyclotomic_ker_le_of_tame {C : Type*} [Group C] (χ : G →* C)
    (hχ : localTameAbelianInertiaGroup v ≤ χ.ker) :
    (LocalCyclotomic.inertiaCharacter p).ker ≤ (χ.comp (I).subtype).ker := by
  rw [inertiaCyclotomic_ker_eq_tame]
  exact fun _ hg ↦ hχ hg

/-- The cyclotomic inertia kernel is open in the original Krull topology. -/
theorem inertiaCyclotomic_ker_isOpen :
    IsOpen ((LocalCyclotomic.inertiaCharacter p).ker : Set I) := by
  have he : (LocalCyclotomic.inertiaCharacter p).ker =
      (tameCharacter v).ker := by
    rw [inertiaCyclotomic_ker_eq_tame,
      localTameAbelianInertiaGroup_subgroupOf_eq_tameCharacter_ker]
  rw [he]
  have hs := (ContinuousSMulDiscrete.isOpen_smul_eq G
    (tameUniformizerRoot v) (tameUniformizerRoot v)).preimage
      (show Continuous (fun g : I ↦ (g : G)) from continuous_subtype_val)
  convert hs using 1
  ext g
  exact tameCharacter_eq_one_iff v g

/-- Every prime-field inertia character with open kernel kills the cyclotomic kernel. -/
theorem inertiaCyclotomic_ker_le_primeField (χ : I →* (ZMod p)ˣ)
    (hχ : IsOpen (χ.ker : Set I)) :
    (LocalCyclotomic.inertiaCharacter p).ker ≤ χ.ker := by
  let : CharP (IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)) p :=
    charP_of_injective_ringHom (LocalCyclotomic.residueEquiv p).symm.toRingHom.injective p
  have hc : p.Coprime (Nat.card ((ZMod p)ˣ × (ZMod p)ˣ)) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card_units]
    have hp := (Fact.out : p.Prime).two_le
    have hcop : p.Coprime (p - 1) := by
      exact (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_one_right p)
    exact hcop.mul_right hcop
  let θ := LocalCyclotomic.inertiaCharacter p
  let : IsCyclic (θ.prod χ).range :=
    LocalRamification.isCyclic_inertia_range_of_coprime v (p := p) Fact.out (θ.prod χ)
      (by simpa only [MonoidHom.ker_prod, Subgroup.coe_inf] using
        (inertiaCyclotomic_ker_isOpen p).inter hχ) hc
  exact ker_le_of_cyclic_pair θ χ (LocalCyclotomic.inertiaCharacter_surjective p)

/-- Normalization for actual prime-field characters requires no kernel-containment input. -/
theorem exists_primeField_inertia_exponent (χ : I →* (ZMod p)ˣ)
    (hχ : IsOpen (χ.ker : Set I)) :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ p - 1 ∧ ∀ g, χ g = LocalCyclotomic.inertiaCharacter p g ^ b := by
  simpa using exists_coefficient_character_pow (RingHom.id (ZMod p))
    (LocalCyclotomic.inertiaCharacter p) χ (LocalCyclotomic.inertiaCharacter_surjective p)
      (inertiaCyclotomic_ker_le_primeField p χ hχ)

/-- For a continuous prime-field inertia character, openness is automatic. -/
theorem inertiaCyclotomic_ker_le_continuous (χ : I →* (ZMod p)ˣ)
    (hχ : Continuous χ) : (LocalCyclotomic.inertiaCharacter p).ker ≤ χ.ker :=
  inertiaCyclotomic_ker_le_primeField p χ (isOpen_discrete {1} |>.preimage hχ)

end GaloisRepresentation.SerreWeight
