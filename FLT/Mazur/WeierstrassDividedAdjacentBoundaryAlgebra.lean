/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPreviousBoundaryAlgebra
public import FLT.Mazur.WeierstrassSuccessiveXTensorOverlap

/-!
# The actual adjacent horizontal transition with both parameter corrections

Correct the original multiplicative scale and the next divided coefficients,
then base change the genuine integral preceding-boundary equivalence.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k * π) d.b3 d.b4 d.b6
local notation "B" => Coordinate W (π ^ (k + 1)) π e.b3 e.b4 e.b6
local notation "x" => WeierstrassDilatation.x W (π ^ k * π) d.b3 d.b4 d.b6
local notation "u₀" => coord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 2
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ k * π) (π ^ (k + 1))
  d.b3 d.b4 d.b6 d.b3 d.b4 d.b6 (Eq.symm (pow_succ π k)) rfl rfl rfl
local notation "q" => WeierstrassDilatation.parameterEquiv W (π ^ (k + 1)) (π ^ (k + 1))
  d.b3 d.b4 d.b6 (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)

/-- The integral adjacent horizontal transition, including the original power identity. -/
def adjacentBoundaryEquiv : Localization.Away x ≃ₐ[R] Localization.Away u₀ :=
  (WeierstrassDilatation.horizontalParameterEquiv W (π ^ k * π) (π ^ (k + 1))
    d.b3 d.b4 d.b6 d.b3 d.b4 d.b6 (pow_succ π k).symm rfl rfl rfl).trans
      (previousBoundaryEquiv hπ d e)

/-- Every original divided function follows the actual two corrected contractions. -/
theorem adjacentBoundaryEquiv_base (z : A) :
    adjacentBoundaryEquiv hπ d e (algebraMap A _ z) =
      algebraMap B _ (fromDivided W (π ^ (k + 1)) π e.b3 e.b4 e.b6 (q (p z))) := by
  rw [adjacentBoundaryEquiv, AlgEquiv.trans_apply, horizontalParameterEquiv_base,
    previousBoundaryEquiv_base]

variable (S : Type u) [CommRing S] [Algebra R S]
local notation "T₀" => WeierstrassDilatation.ScalarExtension W (π ^ k * π) d.b3 d.b4 d.b6 S
local notation "T₁" => ScalarExtension W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S
local notation "O" => TensorDividedOpen W (π ^ k) π d.b3 d.b4 d.b6 S
local notation "H" => Localization.Away (tensorCoord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S 2)

/-- Base change of the genuine integral adjacent horizontal transition. -/
def tensorAdjacentBoundaryEquiv : O ≃ₐ[S] H :=
  PrincipalOpenTensor.transition S x u₀ (adjacentBoundaryEquiv hπ d e)

/-- The transition retains every original integral localized function. -/
theorem tensorAdjacentBoundaryEquiv_coefficient (z : Localization.Away x) :
    tensorAdjacentBoundaryEquiv hπ d e S (PrincipalOpenTensor.coefficient S x z) =
      PrincipalOpenTensor.coefficient S u₀ (adjacentBoundaryEquiv hπ d e z) :=
  PrincipalOpenTensor.transition_coefficient S x u₀ (adjacentBoundaryEquiv hπ d e) z

/-- The tensor transition on every original unlocalized function. -/
theorem tensorAdjacentBoundaryEquiv_base (z : A) :
    tensorAdjacentBoundaryEquiv hπ d e S (algebraMap T₀ O ((1 : S) ⊗ₜ[R] z)) =
      algebraMap T₁ H ((1 : S) ⊗ₜ[R]
        fromDivided W (π ^ (k + 1)) π e.b3 e.b4 e.b6 (q (p z))) := by
  have hbase := tensorAdjacentBoundaryEquiv_coefficient hπ d e S
    (algebraMap A (Localization.Away x) z)
  rw [adjacentBoundaryEquiv_base] at hbase
  exact (congrArg (tensorAdjacentBoundaryEquiv hπ d e S)
    (PrincipalOpenTensor.coefficient_base (R := R) S x z).symm).trans
      (hbase.trans (PrincipalOpenTensor.coefficient_base (R := R) S u₀ _))

/-- The full inverse comparison also retains the original integral transition. -/
theorem tensorAdjacentBoundaryEquiv_symm_coefficient (z : Localization.Away u₀) :
    (tensorAdjacentBoundaryEquiv hπ d e S).symm (PrincipalOpenTensor.coefficient S u₀ z) =
      PrincipalOpenTensor.coefficient S x ((adjacentBoundaryEquiv hπ d e).symm z) :=
  PrincipalOpenTensor.transition_symm_coefficient S x u₀ (adjacentBoundaryEquiv hπ d e) z

end FLT.Mazur.WeierstrassDividedDepth
