/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedWittResidual
public import FLT.Deformations.WittFlatNonvanishing

/-!
# The full local conditions on the Witt-base lift

The original residual representation, transported along its constructed residue
isomorphism, has an effective universal lift satisfying all four local and
arithmetic conditions. Characteristic zero is exactly the remaining arithmetic
nonvanishing assertion on this particular quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Deformation.WittCoefficients
open GaloisRepresentation CategoryTheory
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
local notation "A" => flatObject p k hdim ρ hp hρ
local notation "σ" => flatLift p k hdim ρ hp hρ
local notation "U" => hardlyArithmeticObject W hp d r₀ hr₀
local notation "J" => hardlyFlatIdeal W hp d r₀ hr₀

/-- The Witt-base lift has the original cyclotomic determinant. -/
theorem flatLift_det (g : Field.absoluteGaloisGroup ℚ) :
    ((σ).val g).val.det = algebraMap W A (hardlyCyclotomicValue (p := p) W g) :=
  hardlyFlatLift_det W hp d r₀ hr₀ g

/-- The same lift is unramified away from 2p. -/
theorem flatLift_unramified (q : ℕ) (hq : q.Prime) (hgood : q ≠ 2 ∧ q ≠ p) :
    (FramedGaloisRep.ofGL (σ).val).IsUnramifiedAt
      hq.toHeightOneSpectrumRingOfIntegersRat :=
  hardlyFlatLift_unramified W hp d r₀ hr₀ q hq hgood

/-- Its specified quotient row at two is retained. -/
theorem flatLift_row (g : Field.absoluteGaloisGroup ℚ_[2]) (j : Fin 2) :
    (σ).val (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 1 j =
      if j = 1 then algebraMap W A (hardlyTwoIntegralCharacter W hp d r₀ hr₀ g : W)
      else 0 :=
  hardlyFlatLift_row W hp d r₀ hr₀ g j

/-- Finite-flat open reductions hold on this very lift. -/
theorem flatLift_isFlat :
    (FramedGaloisRep.ofGL (σ).val).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) :=
  hardlyFlatLift_isFlat W hp d r₀ hr₀

/-- The full Witt-base lift has characteristic-zero coefficients exactly at the arithmetic gate. -/
theorem flatObject_charZero_iff : CharZero A ↔ ∀ m : ℕ, (p : U) ^ m ∉ J :=
  wittFlat_charZero_iff p k U _ _ (hardlyFlatIdeal_ne_top W hp d r₀ hr₀)

/-- A continuous characteristic-zero specialization exists exactly when all powers survive. -/
theorem flatObject_exists_charZero_iff :
    (∃ B : ProartinianCat W, CharZero B ∧ Nonempty (A ⟶ B)) ↔
      ∀ m : ℕ, (p : U) ^ m ∉ J :=
  wittFlat_exists_charZero_iff p k U _ _ (hardlyFlatIdeal_ne_top W hp d r₀ hr₀)

end Deformation.WittCoefficients
