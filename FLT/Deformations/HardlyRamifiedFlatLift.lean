/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FlatClosedCondition
public import FLT.Deformations.HardlyRamifiedFlatQuotient

/-!
# All equation and flatness conditions on the HR universal lift

The lift on the further quotient retains the determinant, inertia and local
quotient equations and has finite-flat reductions at p simultaneously.
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
local notation "U" => hardlyArithmeticObject O hp hdim ρ hρ
local notation "r" => FramedGaloisRep.ofGL (Subtype.val (hardlyArithmeticLift O hp hdim ρ hρ))
local notation "v" => Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)

/-- Maps from the actual flat quotient classify flat arithmetic specializations. -/
def hardlyFlatParameterEquiv (A : ProartinianCat O) :
    (hardlyFlatObject O hp hdim ρ hρ ⟶ A) ≃
      {f : U ⟶ A // ((r).baseChange f.hom.toRingHom f.hom.cont).IsFlatAt v} :=
  flatClosedEquiv U v r ⟨_, hardlyArithmetic_residual_mem O hp hdim ρ hρ⟩
    (hardlyFlatIdeal_ne_top O hp hdim ρ hρ) A

/-- The universal framed lift retains its original residual representation. -/
def hardlyFlatLift : ContinuousFramedLifts O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ) (hardlyFlatObject O hp hdim ρ hρ) :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _ (hardlyFlatProjection O hp hdim ρ hρ)).val

/-- The classified framed lift is the actual coefficient specialization. -/
theorem hardlyFlatLift_eq :
    FramedGaloisRep.ofGL (hardlyFlatLift O hp hdim ρ hρ).val =
      hardlyFlatRepresentation O hp hdim ρ hρ := by
  apply FramedGaloisRep.GL.injective
  ext g i j
  simp only [FramedGaloisRep.ofGL, Equiv.apply_symm_apply,
    hardlyFlatRepresentation, flatClosedRepresentation, FramedGaloisRep.baseChange_GL]
  rfl

/-- Finite flatness holds on this same framed universal arithmetic lift. -/
theorem hardlyFlatLift_isFlat :
    (FramedGaloisRep.ofGL (hardlyFlatLift O hp hdim ρ hρ).val).IsFlatAt v := by
  rw [hardlyFlatLift_eq]
  exact hardlyFlatRepresentation_isFlat O hp hdim ρ hρ

/-- The full lift has the original cyclotomic determinant. -/
theorem hardlyFlatLift_det (g : Field.absoluteGaloisGroup ℚ) :
    ((hardlyFlatLift O hp hdim ρ hρ).val g).val.det =
      algebraMap O (hardlyFlatObject O hp hdim ρ hρ)
        (hardlyCyclotomicValue (p := p) O g) :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _
    (hardlyFlatProjection O hp hdim ρ hρ)).property.1 g

/-- The full lift is unramified away from 2p. -/
theorem hardlyFlatLift_unramified (q : ℕ) (hq : q.Prime) (hgood : q ≠ 2 ∧ q ≠ p) :
    (FramedGaloisRep.ofGL (hardlyFlatLift O hp hdim ρ hρ).val).IsUnramifiedAt
      hq.toHeightOneSpectrumRingOfIntegersRat :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _
    (hardlyFlatProjection O hp hdim ρ hρ)).property.2.1 q hq hgood

/-- The full lift retains the specified quotient character at two. -/
theorem hardlyFlatLift_row (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    (hardlyFlatLift O hp hdim ρ hρ).val
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
        if j = 1 then algebraMap O (hardlyFlatObject O hp hdim ρ hρ)
          (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) else 0 :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ _
    (hardlyFlatProjection O hp hdim ρ hρ)).property.2.2 g j

end Deformation
