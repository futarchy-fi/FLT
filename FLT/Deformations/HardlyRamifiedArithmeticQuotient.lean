/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedArithmeticResidual
public import FLT.Deformations.UniversalArithmeticQuotient

/-!
# Determinant and unramifiedness on the actual HR quotient

Starting with the original HR representation, construct the simultaneous
quotient with cyclotomic determinant, unramifiedness away from 2p and the
specified quadratic quotient at two. Flatness at p is not asserted here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)

/-- The actual HR equation quotient; all its residual equations are theorems. -/
def hardlyArithmeticObject : ProartinianCat O :=
  universalArithmeticObject O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ) (hardlyCyclotomicValue (p := p) O)
    (hardlyAwayInertia p) (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])).toMonoidHom
    (hardlyTwoIntegralCharacter O hp hdim ρ hρ) 1
    (hardlyTwoFramedResidual_det O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_away O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_row O hp hdim ρ hρ)

/-- Its maps classify the actual determinant, arithmetic inertia and fixed quotient conditions. -/
def hardlyArithmeticEquiv (A : ProartinianCat O) :
    (hardlyArithmeticObject O hp hdim ρ hρ ⟶ A) ≃
      {τ : ContinuousFramedLifts O (Field.absoluteGaloisGroup ℚ) (Fin 2)
          (hardlyTwoFramedResidual O hp hdim ρ hρ) A //
        (∀ g, (τ.val g : Matrix (Fin 2) (Fin 2) A).det =
          algebraMap O A (hardlyCyclotomicValue (p := p) O g)) ∧
        (∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ p →
          (FramedGaloisRep.ofGL τ.val).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat) ∧
        (∀ g j, τ.val (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
          if j = 1 then algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)
          else 0)} :=
  (universalArithmeticEquiv O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ) (hardlyCyclotomicValue (p := p) O)
    (hardlyAwayInertia p) (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])).toMonoidHom
    (hardlyTwoIntegralCharacter O hp hdim ρ hρ) 1
    (hardlyTwoFramedResidual_det O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_away O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_row O hp hdim ρ hρ) A).trans
    (Equiv.subtypeEquivRight fun τ ↦ and_congr_right fun _ ↦
      and_congr (by simpa only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply] using
        trivial_hardlyAwayInertia_iff p (FramedGaloisRep.ofGL τ.val)) Iff.rfl)

/-- This is a further quotient of the existing HR object at two. -/
def hardlyArithmeticFromTwo :
    hardlyTwoUniversalObject O hp hdim ρ hρ ⟶ hardlyArithmeticObject O hp hdim ρ hρ :=
  universalArithmeticToLocal O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ) (hardlyCyclotomicValue (p := p) O)
    (hardlyAwayInertia p) (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])).toMonoidHom
    (hardlyTwoIntegralCharacter O hp hdim ρ hρ) 1
    (hardlyTwoFramedResidual_det O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_away O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_row O hp hdim ρ hρ)

/-- The map from the original HR object at two is surjective. -/
theorem hardlyArithmeticFromTwo_surjective :
    Function.Surjective (hardlyArithmeticFromTwo O hp hdim ρ hρ).hom :=
  universalArithmeticToLocal_surjective O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ) (hardlyCyclotomicValue (p := p) O)
    (hardlyAwayInertia p) (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])).toMonoidHom
    (hardlyTwoIntegralCharacter O hp hdim ρ hρ) 1
    (hardlyTwoFramedResidual_det O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_away O hp hdim ρ hρ)
    (hardlyTwoFramedResidual_row O hp hdim ρ hρ)

/-- The universal lift on the constructed arithmetic quotient. -/
def hardlyArithmeticLift : ContinuousFramedLifts O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ) (hardlyArithmeticObject O hp hdim ρ hρ) :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _ (𝟙 _)).val

/-- Every classified lift is obtained by specializing that very universal lift. -/
theorem hardlyArithmeticEquiv_apply (A : ProartinianCat O)
    (f : hardlyArithmeticObject O hp hdim ρ hρ ⟶ A)
    (g : Field.absoluteGaloisGroup ℚ) (i j : Fin 2) :
    (hardlyArithmeticEquiv O hp hdim ρ hρ A f).val.val g i j =
      f.hom ((hardlyArithmeticLift O hp hdim ρ hρ).val g i j) := rfl

/-- The universal representation has cyclotomic determinant. -/
theorem hardlyArithmeticLift_det (g : Field.absoluteGaloisGroup ℚ) :
    ((hardlyArithmeticLift O hp hdim ρ hρ).val g).val.det =
      algebraMap O (hardlyArithmeticObject O hp hdim ρ hρ)
        (hardlyCyclotomicValue (p := p) O g) :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _ (𝟙 _)).property.1 g

/-- The universal representation is unramified at every prime away from 2p. -/
theorem hardlyArithmeticLift_unramified (q : ℕ) (hq : q.Prime) (hgood : q ≠ 2 ∧ q ≠ p) :
    (FramedGaloisRep.ofGL (hardlyArithmeticLift O hp hdim ρ hρ).val).IsUnramifiedAt
      hq.toHeightOneSpectrumRingOfIntegersRat :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _ (𝟙 _)).property.2.1 q hq hgood

/-- The same universal representation retains the specified quotient at two. -/
theorem hardlyArithmeticLift_row (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    (hardlyArithmeticLift O hp hdim ρ hρ).val
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
        if j = 1 then algebraMap O (hardlyArithmeticObject O hp hdim ρ hρ)
          (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) else 0 :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _ (𝟙 _)).property.2.2 g j

end Deformation
