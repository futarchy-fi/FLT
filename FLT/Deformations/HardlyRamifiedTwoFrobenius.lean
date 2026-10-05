/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedArithmeticResidual
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusTraces
public import FLT.AbsoluteGaloisGroup.CyclotomicCharacterNaturality
public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero

/-! # A separated Frobenius eigenvalue for the specified quotient at two -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open GaloisRepresentation IsDedekindDomain
attribute [local instance 2000] HeightOneSpectrum.adicCompletion.instField
  HeightOneSpectrum.instAlgebraAdicCompletion
namespace Deformation

/-- There is a local element at two with cyclotomic value exactly two. -/
theorem exists_two_cyclotomic_value (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ∃ g : Field.absoluteGaloisGroup ℚ_[2],
      (cyclotomicCharacter (AlgebraicClosure ℚ) p
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g).toRingEquiv : ℤ_[p]) = 2 := by
  obtain ⟨e, _, _⟩ := ThreeAdicPlan.exists_completionTwoEquiv
  let σ := Field.AbsoluteGaloisGroup.adicArithFrob ThreeAdicPlan.twoAdicPlace
  refine ⟨Field.absoluteGaloisGroup.map e.symm.toRingHom σ, ?_⟩
  rw [cyclotomicCharacter.absoluteGalois_map, cyclotomicCharacter.absoluteGalois_map,
    ← cyclotomicCharacter.absoluteGalois_map p
      (algebraMap ℚ (ThreeAdicPlan.twoAdicPlace.adicCompletion ℚ)) σ]
  exact B5Inputs.cyclotomicCharacter_adicArithFrob p 2 Nat.prime_two
    (by obtain ⟨n, hn⟩ := hp; omega)

open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O]
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "k" => residueField (𝓞 := O)

/-- The two residual Frobenius eigencharacters differ by a unit. -/
theorem exists_hardlyTwoResidual_gap :
    ∃ g : Field.absoluteGaloisGroup ℚ_[2], IsUnit
      (hardlyTwoFramedResidual O hp hdim ρ hρ
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 0 0 -
          algebraMap O k (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)) := by
  obtain ⟨g, hg⟩ := exists_two_cyclotomic_value p hp
  refine ⟨g, isUnit_iff_ne_zero.mpr ?_⟩
  let s := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g
  let c : k := algebraMap O k (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)
  have hc : c ^ 2 = 1 := by
    have he := congrArg (fun u : Oˣ ↦ algebraMap O k (u : O))
      (quadraticCharacterLift_sq (hardlyTwoCharacter O hp hdim ρ hρ)
        (hardlyTwoCharacter_sq O hp hdim ρ hρ) O g)
    simpa only [c, hardlyTwoIntegralCharacter, Units.val_pow_eq_pow_val, map_pow,
      Units.val_one, map_one] using he
  have hd := hardlyTwoFramedResidual_det O hp hdim ρ hρ s
  rw [Matrix.det_fin_two, hardlyTwoFramedResidual_row O hp hdim ρ hρ g 0,
    hardlyTwoFramedResidual_row O hp hdim ρ hρ g 1] at hd
  have hv : hardlyCyclotomicValue (p := p) O s = 2 := by
    unfold hardlyCyclotomicValue
    rw [hg, map_ofNat]
  rw [hv] at hd
  simp only [Fin.isValue, zero_ne_one, ↓reduceIte, mul_zero, sub_zero, map_ofNat] at hd
  change _ * c = 2 at hd
  intro hz
  change _ - c = 0 at hz
  have hzero : (1 : k) = 0 := by linear_combination hc + hz * c - hd
  exact one_ne_zero hzero

end Deformation
