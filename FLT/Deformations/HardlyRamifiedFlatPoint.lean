/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedFlatLift
public import FLT.Deformations.FlatQuotientNonvanishing

/-!
# Constructing a point of the actual hardly ramified flat quotient

A framed lift with the prescribed residual representation and the four
separate local conditions gives an explicit continuous coefficient map.
Its characteristic-zero target then detects every power of p. This is a
constructor from a verified lift, not an existence theorem for such a lift.
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
variable (A : ProartinianCat O)
  (τ : ContinuousFramedLifts O (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual O hp hdim ρ hρ) A)
  (hdet : ∀ g, (τ.val g : Matrix (Fin 2) (Fin 2) A).det =
    algebraMap O A (hardlyCyclotomicValue (p := p) O g))
  (haway : ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ p →
    (FramedGaloisRep.ofGL τ.val).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat)
  (hrow : ∀ g j, τ.val (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
    if j = 1 then algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) else 0)

/-- The arithmetic parameter map attached to the given residual-compatible lift. -/
def hardlyArithmeticPoint : U ⟶ A :=
  (hardlyArithmeticEquiv O hp hdim ρ hρ A).symm ⟨τ, hdet, haway, hrow⟩

/-- Specializing the arithmetic universal representation recovers this very lift. -/
theorem hardlyArithmeticPoint_rep :
    (r).baseChange (hardlyArithmeticPoint O hp hdim ρ hρ A τ hdet haway hrow).hom.toRingHom
      (hardlyArithmeticPoint O hp hdim ρ hρ A τ hdet haway hrow).hom.cont =
      FramedGaloisRep.ofGL τ.val := by
  have he := (hardlyArithmeticEquiv O hp hdim ρ hρ A).apply_symm_apply
    ⟨τ, hdet, haway, hrow⟩
  apply FramedGaloisRep.GL.injective
  ext g i j
  have hh := congrArg (fun t ↦ t.val.val g i j) he
  rw [hardlyArithmeticEquiv_apply] at hh
  simpa only [FramedGaloisRep.baseChange_GL, FramedGaloisRep.ofGL,
    Equiv.apply_symm_apply, hardlyArithmeticPoint, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    ContinuousAlgHom.coe_coe] using hh

variable (hflat : (FramedGaloisRep.ofGL τ.val).IsFlatAt
  (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)))
include hdet haway hrow hflat

/-- Flatness of the chosen lift kills the actual defining ideal, not just its residue. -/
theorem hardlyArithmeticPoint_kills_flatIdeal :
    hardlyFlatIdeal O hp hdim ρ hρ ≤
      RingHom.ker (hardlyArithmeticPoint O hp hdim ρ hρ A τ hdet haway hrow).hom.toRingHom := by
  exact flatReductionIdeal_le_ker U v r
    (hardlyArithmeticPoint O hp hdim ρ hρ A τ hdet haway hrow)
    ((hardlyArithmeticPoint_rep O hp hdim ρ hρ A τ hdet haway hrow).symm ▸ hflat)

/-- The resulting continuous map from the actual HR flat quotient. -/
def hardlyFlatPoint : hardlyFlatObject O hp hdim ρ hρ ⟶ A :=
  factorClosedIdeal U (hardlyFlatIdeal O hp hdim ρ hρ)
    (hardlyFlatIdeal_closed O hp hdim ρ hρ) (hardlyFlatIdeal_ne_top O hp hdim ρ hρ)
    (hardlyArithmeticPoint O hp hdim ρ hρ A τ hdet haway hrow)
    (hardlyArithmeticPoint_kills_flatIdeal O hp hdim ρ hρ A τ hdet haway hrow hflat)

/-- The constructed map factors the arithmetic parameter map exactly. -/
theorem hardlyFlatPoint_comp :
    hardlyFlatProjection O hp hdim ρ hρ ≫
      hardlyFlatPoint O hp hdim ρ hρ A τ hdet haway hrow hflat =
      hardlyArithmeticPoint O hp hdim ρ hρ A τ hdet haway hrow :=
  quotient_comp_factorClosedIdeal _ _ _ _ _ _

/-- Its characteristic-zero target detects every p-power in the actual arithmetic ring. -/
theorem hardlyFlatPoint_powers_avoid [CharZero A] :
    ∀ m : ℕ, (p : U) ^ m ∉ hardlyFlatIdeal O hp hdim ρ hρ :=
  flatClosed_powers_avoid_of_charZero U v r (hardlyFlatIdeal_ne_top O hp hdim ρ hρ) p
    (hardlyFlatPoint O hp hdim ρ hρ A τ hdet haway hrow hflat).hom.toRingHom
    (Fact.out : p.Prime).ne_zero

end Deformation
