/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.CharacterModels
public import FLT.GaloisRepresentation.HardlyRamified.ResidualGlobalModel
public import FLT.GaloisRepresentation.HardlyRamified.FlatCoefficientExtension

/-!
# Global finite-level models of integral characters

Finite quotients of a continuous integral character form finite Galois modules.
Flatness at three and unramifiedness outside three give global models over
`ℤ[1/2]`. Three-primary quotients lie in category D because dyadic inertia is trivial.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local notation "Γ" => Field.absoluteGaloisGroup ℚ

variable {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]

/-- The character obtained by reducing coefficients modulo an ideal. -/
def quotientCharacter (ψ : Γ →* Oˣ) (I : Ideal O) : Γ →* (O ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).comp ψ

/-- The finite Galois module carried by an open finite coefficient quotient. -/
def characterQuotientModule (ψ : Γ →* Oˣ) (hc : Continuous ψ)
    (I : Ideal O) (hI : IsOpen (I : Set O)) [Finite (O ⧸ I)] :
    FiniteContinuousGaloisModule := by
  let instDiscrete : DiscreteTopology (O ⧸ I) := QuotientAddGroup.discreteTopology hI
  refine { Carrier := CharacterSpace (quotientCharacter ψ I)
           finite := inferInstanceAs (Finite (O ⧸ I))
           continuous := ⟨fun x y ↦ ?_⟩ }
  change IsOpen {σ : Γ | Ideal.Quotient.mk I (ψ σ : O) * x.val = y.val}
  exact (isOpen_discrete ({y.val} : Set (O ⧸ I))).preimage
    (((QuotientRing.isOpenQuotientMap_mk I).continuous.comp
      (Units.continuous_val.comp hc)).mul_const x.val)

/-- Unramifiedness of an integral character descends to every finite quotient module. -/
theorem characterQuotient_unramified_of_character
    (ψ : Γ →* Oˣ) (hc : Continuous ψ) (hu : UnramifiedOutsideThree ψ)
    (I : Ideal O) (hI : IsOpen (I : Set O)) [Finite (O ⧸ I)] :
    UnramifiedOutside {3} (characterQuotientModule ψ hc I hI) := by
  constructor
  intro p hp hp3 σ hσ x
  have hg := hu p hp (by simpa using hp3) hσ
  change ψ (Field.absoluteGaloisGroup.map
    (algebraMap ℚ (hp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) σ) = 1 at hg
  change Ideal.Quotient.mk I (ψ (Field.absoluteGaloisGroup.map
    (algebraMap ℚ (hp.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) σ) : O) *
      (show O ⧸ I from x) = (show O ⧸ I from x)
  rw [hg, Units.val_one, map_one, one_mul]

/-- Finite flatness at three gives a three-adic integral model of each finite quotient. -/
theorem characterQuotient_localModel_of_flat
    (ψ : Γ →* Oˣ) (hc : Continuous ψ) (hf : Flat3 ψ)
    (I : Ideal O) (hI : IsOpen (I : Set O)) [Finite (O ⧸ I)] :
    Nonempty (HasFiniteFlatModel ℤ_[3] (characterQuotientModule ψ hc I hI).localAtThree) := by
  let W := characterQuotientModule ψ hc I hI
  have hflat : GaloisModule.IsFiniteFlat (threeAdicPlace.adicCompletionIntegers ℚ)
      (threeAdicPlace.adicCompletion ℚ) (AlgebraicClosure (threeAdicPlace.adicCompletion ℚ))
      (W.restrict (algebraMap ℚ (threeAdicPlace.adicCompletion ℚ))) :=
    hf I hI
  obtain ⟨M⟩ := (nonempty_hasFiniteFlatModel_iff _).mpr hflat
  apply localThreeModel_transport W
  convert M using 1
  congr 3
  exact Subsingleton.elim _ _

/-- A three-primary character quotient with trivial dyadic inertia lies in category D. -/
theorem characterQuotient_inCategoryD_of_power
    (ψ : Γ →* Oˣ) (hc : Continuous ψ) (hu : UnramifiedOutsideThree ψ)
    (I : Ideal O) (hI : IsOpen (I : Set O)) [Finite (O ⧸ I)]
    (n : ℕ) (hn : (3 : O) ^ n ∈ I)
    (M : ModelOverZInvTwo (characterQuotientModule ψ hc I hI)) :
    InCategoryD (FiniteFlatObject.ofModel M) := by
  let W := characterQuotientModule ψ hc I hI
  have hcast : (3 : O ⧸ I) ^ n = 0 := by
    simpa only [map_pow, map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem.mpr hn)
  have hkillQ (x : O ⧸ I) : (3 ^ n) • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (O ⧸ I), Nat.cast_pow, Nat.cast_ofNat, hcast, zero_smul]
  have hkill (x : W) : (3 ^ n) • x = 0 := hkillQ x
  have hpgroup : IsPGroup 3 (Multiplicative W) :=
    isPGroup_iff_pow_pow_eq_one.mpr (fun x ↦ ⟨n, hkill x⟩)
  constructor
  · exact hpgroup.exists_card_eq
  · intro σ hσ x
    have hfix := (characterQuotient_unramified_of_character ψ hc hu I hI).inertia_trivial
      2 Nat.prime_two (by decide) σ hσ
    apply sub_eq_zero.mpr
    convert hfix (Field.absoluteGaloisGroup.map
      (@algebraMap ℚ _ _ _
        (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion _ _ _)) σ • x - x)
      using 1
    · rfl
    · congr 3
      exact Subsingleton.elim _ _

/-- Each bounded three-primary quotient of a flat unramified character has a category-D model. -/
theorem characterQuotient_globalModel_of_flat_unramified
    (ψ : Γ →* Oˣ) (hc : Continuous ψ) (hf : Flat3 ψ) (hu : UnramifiedOutsideThree ψ)
    (I : Ideal O) (hI : IsOpen (I : Set O)) [Finite (O ⧸ I)]
    (n : ℕ) (hn : (3 : O) ^ n ∈ I) :
    Nonempty (DModel (characterQuotientModule ψ hc I hI)) := by
  obtain ⟨M₃⟩ := characterQuotient_localModel_of_flat ψ hc hf I hI
  have hur := (characterQuotient_unramified_of_character ψ hc hu I hI).mono
    (show ({3} : Finset ℕ) ⊆ {2, 3} by decide)
  obtain ⟨M⟩ := global_model_away_two _ M₃ hur
  exact ⟨{ toModelOverZInvTwo := M
           inCategoryD := characterQuotient_inCategoryD_of_power ψ hc hu I hI n hn M }⟩

end ThreeAdicPlan
