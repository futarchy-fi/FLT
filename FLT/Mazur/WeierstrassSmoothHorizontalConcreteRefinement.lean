/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalProductResidue

/-!
# Concrete ordinary and output refinements of the initial conic action source

The integral product inputs and both residue parameters have been constructed.
Applying the secant and horizontal localization constructions now supplies
both output residue maps from these actual inputs, with no presentation or
factorization hypothesis supplied by the caller.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "S" => SmoothHorizontalProductRing W (π ^ k)
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "ψ" => smoothHorizontalInput W (π ^ k)
open WeierstrassModificationReesCoordinates WeierstrassModificationX

/-- The first constructed residue product has the original zero tangent branch. -/
theorem smoothHorizontalFirstResidue_branch :
    e₁ (ψ (horizontalVertical W (π ^ k))) = 0 := by
  rw [smoothHorizontalFirstResidue_input]
  exact (congrArg (smoothHorizontalResidueConic D)
    (horizontalConicFirstResidue_slope D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)).trans (map_zero _)

/-- The opposite constructed residue product has the original negative tangent branch. -/
theorem smoothHorizontalSecondResidue_branch :
    e₂ (ψ (horizontalVertical W (π ^ k))) = -e₂ (algebraMap R S W.a₁) := by
  rw [smoothHorizontalSecondResidue_input, AlgHom.commutes]
  have h := congrArg (smoothHorizontalResidueConic D)
    (horizontalConicSecondResidue_slope D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
  refine h.trans ?_
  rw [map_neg]
  change -smoothHorizontalResidueConic D
    (algebraMap K K[T;T⁻¹] (residue R W.a₁)) = -algebraMap R C W.a₁
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R K C, ResidueField.algebraMap_eq]

omit [IsDomain R] [IsLocalRing R] in
/-- The squared divided coefficient supplies the linear center factorization. -/
theorem smoothHorizontal_factor6 : W.a₆ = π ^ k * (π ^ k * d.b6) := by
  rw [d.factor6, pow_two, mul_assoc]

local notation "a₀" => smoothHorizontalLeft W (π ^ k)
local notation "c₀" => smoothHorizontalRight W (π ^ k)
local notation "v₀" => smoothHorizontalY W (π ^ k)
local notation "p" => smoothHorizontalPoint W (π ^ k)
local notation "ha" => smoothHorizontalLeft_inclusion W (π ^ k)
local notation "hp" => smoothHorizontal_structure W (π ^ k)
local notation "hv" => smoothHorizontal_common W (π ^ k)
local notation "hc" => smoothHorizontalRight_contraction W (π ^ k)
local notation "hf" => smoothHorizontalInput_flat W (π ^ k)

/-- The first actual residue product factors through the genuine output horizontal open. -/
def smoothHorizontalFirstOutputResidue :=
  secantHorizontalResidueFactor W π D d (Nat.le_of_lt hk) (by omega)
    d.b3 d.b4 (π ^ k * d.b6) d.factor3 d.factor4 (smoothHorizontal_factor6 d)
    a₀ c₀ v₀ p ha hp hv ψ hc hf (e₁).toRingHom
    (smoothHorizontalFirstResidue_denominator D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (smoothHorizontalFirstResidue_maximal D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (Or.inl (smoothHorizontalFirstResidue_branch D d hk0 hk hπ))

/-- The opposite actual residue product factors through the same genuine output open. -/
def smoothHorizontalSecondOutputResidue :=
  secantHorizontalResidueFactor W π D d (Nat.le_of_lt hk) (by omega)
    d.b3 d.b4 (π ^ k * d.b6) d.factor3 d.factor4 (smoothHorizontal_factor6 d)
    a₀ c₀ v₀ p ha hp hv ψ hc hf (e₂).toRingHom
    (smoothHorizontalSecondResidue_denominator D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (smoothHorizontalSecondResidue_maximal D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (Or.inr (smoothHorizontalSecondResidue_branch D d hk0 hk hπ))

/-- The first concrete output factor recovers every original integral product function. -/
theorem smoothHorizontalFirstOutputResidue_base (q : SmoothHorizontalProductRing W (π ^ k)) :
    smoothHorizontalFirstOutputResidue D d hk0 hk hπ (algebraMap S _ q) = e₁ q :=
  secantHorizontalResidueFactor_base ..

/-- The opposite concrete output factor recovers every original integral product function. -/
theorem smoothHorizontalSecondOutputResidue_base (q : SmoothHorizontalProductRing W (π ^ k)) :
    smoothHorizontalSecondOutputResidue D d hk0 hk hπ (algebraMap S _ q) = e₂ q :=
  secantHorizontalResidueFactor_base ..

end FLT.Mazur.WeierstrassIntegralChart
