/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedFlatPoint
public import FLT.Deformations.HardlyRamifiedWittLift

/-!
# The characteristic-zero point criterion on the actual Witt-base quotient

This connects a residual-compatible framed lift and its separately verified
local conditions to the D1a nonvanishing gate. Constructing that lift remains
an arithmetic existence problem; no characteristic-zero point is assumed
as a field of a new structure.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Deformation.WittCoefficients
open CategoryTheory GaloisRepresentation
namespace Deformation.WittCoefficients
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Finite k]
  [Algebra ℤ_[p] k] [TopologicalSpace k] [IsTopologicalRing k] [DiscreteTopology k]
  {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
  (hdim : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
  (hp : Odd p) (hρ : IsHardlyRamified hp hdim ρ)
local notation "W" => WittVector p k
local notation "r₀" => residualRep p k ρ
local notation "hr₀" => residual_hardlyRamified p k hdim ρ hp hρ
local notation "d" => residual_rank p k hdim
variable (B : ProartinianCat (WittVector p k))
  (τ : ContinuousFramedLifts (WittVector p k) (Field.absoluteGaloisGroup ℚ) (Fin 2)
    (hardlyTwoFramedResidual (WittVector p k) hp (residual_rank p k hdim)
      (residualRep p k ρ) (residual_hardlyRamified p k hdim ρ hp hρ)) B)
  (hdet : ∀ g, (τ.val g : Matrix (Fin 2) (Fin 2) B).det =
    algebraMap (WittVector p k) B (hardlyCyclotomicValue (p := p) (WittVector p k) g))
  (haway : ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ p →
    (FramedGaloisRep.ofGL τ.val).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat)
  (hrow : ∀ g j, τ.val (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
    if j = 1 then algebraMap (WittVector p k) B
      (hardlyTwoIntegralCharacter (WittVector p k) hp (residual_rank p k hdim)
        (residualRep p k ρ) (residual_hardlyRamified p k hdim ρ hp hρ) g : WittVector p k)
    else 0)
  (hflat : (FramedGaloisRep.ofGL τ.val).IsFlatAt
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)))

include τ hdet haway hrow hflat

/-- The continuous specialization has exactly the original Witt-base flat quotient as source. -/
def flatPointOfFramedLift : flatObject p k hdim ρ hp hρ ⟶ B :=
  hardlyFlatPoint W hp d r₀ hr₀ B τ hdet haway hrow hflat

/-- A verified characteristic-zero framed lift proves the precise D1a ideal exclusion. -/
theorem flatIdeal_powers_avoid_of_framedLift [CharZero B] :
    ∀ m : ℕ, (p : hardlyArithmeticObject W hp d r₀ hr₀) ^ m ∉
      hardlyFlatIdeal W hp d r₀ hr₀ :=
  hardlyFlatPoint_powers_avoid W hp d r₀ hr₀ B τ hdet haway hrow hflat

/-- The same hypotheses prove characteristic zero of the constructed flat coefficient ring. -/
theorem flatObject_charZero_of_framedLift [CharZero B] :
    CharZero (flatObject p k hdim ρ hp hρ) :=
  (flatObject_charZero_iff p k hdim ρ hp hρ).mpr
    (flatIdeal_powers_avoid_of_framedLift p k hdim ρ hp hρ B τ hdet haway hrow hflat)

end Deformation.WittCoefficients
