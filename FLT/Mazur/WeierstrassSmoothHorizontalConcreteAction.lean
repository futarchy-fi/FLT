/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalResidueCoordinates
public import FLT.Mazur.WeierstrassSecantHorizontalResidueAction

/-!
# Actual action on the two concrete horizontal conic branches

The output factor maps and smooth tangent unit are constructed from the
integral source. The first branch has character tau, and the opposite branch
has its inverse, with the original signed conic scales and slopes retained.
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

local notation "a₀" => smoothHorizontalLeft W (π ^ k)
local notation "c₀" => smoothHorizontalRight W (π ^ k)
local notation "v₀" => smoothHorizontalY W (π ^ k)
local notation "p" => smoothHorizontalPoint W (π ^ k)
local notation "ha" => smoothHorizontalLeft_inclusion W (π ^ k)
local notation "hp" => smoothHorizontal_structure W (π ^ k)
local notation "hv" => smoothHorizontal_common W (π ^ k)
local notation "hc" => smoothHorizontalRight_contraction W (π ^ k)
local notation "hf" => smoothHorizontalInput_flat W (π ^ k)

/-- The actual smooth action lift on the concrete integral product refinement. -/
def smoothHorizontalActionLift :=
  secantHorizontalActionLift W π d.b3 d.b4 (π ^ k * d.b6)
    d.factor3 d.factor4 (smoothHorizontal_factor6 d)
    a₀ c₀ p ha hp ψ hc hf

local notation "M" => smoothHorizontalActionLift d
omit [IsDomain R] [IsLocalRing R] in
/-- The actual refined action lift preserves the original coefficient map. -/
theorem smoothHorizontalActionLift_coefficient (r : R) :
    M (algebraMap R (HorizontalSourceRing W (π ^ k)) r) = algebraMap R _ r := by
  rw [IsScalarTower.algebraMap_apply R (Coordinate W 2) (HorizontalSourceRing W (π ^ k))]
  have h := secantHorizontalActionLift_base W π d.b3 d.b4 (π ^ k * d.b6)
    d.factor3 d.factor4 (smoothHorizontal_factor6 d) a₀ c₀ p ha hp ψ hc hf
    (algebraMap R (Coordinate W 2) r)
  refine h.trans ?_
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]

local notation "E₁" => smoothHorizontalFirstOutputResidue D d hk0 hk hπ
local notation "E₂" => smoothHorizontalSecondOutputResidue D d hk0 hk hπ
local notation "τ" => smoothHorizontalTangentUnit D

/-- The actual first branch is scaled by the named positive smooth Laurent parameter. -/
theorem smoothHorizontalFirstOutputResidue_action :
    E₁ (M (horizontalScale W (π ^ k))) =
        (τ : C) * e₁ (ψ (horizontalScale W (π ^ k))) ∧
      E₁ (M (horizontalVertical W (π ^ k))) = 0 := by
  exact (secantHorizontalResidueFactor_action W π D d (Nat.le_of_lt hk) (by omega)
    d.b3 d.b4 (π ^ k * d.b6) d.factor3 d.factor4 (smoothHorizontal_factor6 d)
    a₀ c₀ v₀ p ha hp hv ψ hc hf (e₁).toRingHom
    (smoothHorizontalFirstResidue_denominator D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (smoothHorizontalFirstResidue_maximal D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (Or.inl (smoothHorizontalFirstResidue_branch D d hk0 hk hπ)) τ
    (smoothHorizontalFirstResidue_tangent D d hk0 hk hπ)).1
      (smoothHorizontalFirstResidue_branch D d hk0 hk hπ)

/-- The actual opposite branch is scaled by the inverse smooth Laurent parameter. -/
theorem smoothHorizontalSecondOutputResidue_action :
    E₂ (M (horizontalScale W (π ^ k))) =
        (↑τ⁻¹ : C) * e₂ (ψ (horizontalScale W (π ^ k))) ∧
      E₂ (M (horizontalVertical W (π ^ k))) = -algebraMap R C W.a₁ := by
  have h := (secantHorizontalResidueFactor_action W π D d (Nat.le_of_lt hk) (by omega)
    d.b3 d.b4 (π ^ k * d.b6) d.factor3 d.factor4 (smoothHorizontal_factor6 d)
    a₀ c₀ v₀ p ha hp hv ψ hc hf (e₂).toRingHom
    (smoothHorizontalSecondResidue_denominator D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (smoothHorizontalSecondResidue_maximal D k hk0 hk hπ
      d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6)
    (Or.inr (smoothHorizontalSecondResidue_branch D d hk0 hk hπ)) τ
    (smoothHorizontalSecondResidue_tangent D d hk0 hk hπ)).2
      (smoothHorizontalSecondResidue_branch D d hk0 hk hπ)
  exact ⟨h.1, h.2.trans (congrArg Neg.neg ((e₂).commutes W.a₁))⟩

/-- The first output scale retains the original conic parameter and tangent coefficient. -/
theorem smoothHorizontalFirstOutputResidue_scale :
    E₁ (M (horizontalScale W (π ^ k))) = (τ : C) * smoothHorizontalResidueConic D
      (LaurentPolynomial.C (residue R W.a₁) * LaurentPolynomial.T 1) := by
  rw [(smoothHorizontalFirstOutputResidue_action D d hk0 hk hπ).1,
    smoothHorizontalFirstResidue_scale]

/-- The opposite output scale retains its negative tangent coefficient. -/
theorem smoothHorizontalSecondOutputResidue_scale :
    E₂ (M (horizontalScale W (π ^ k))) = (↑τ⁻¹ : C) * smoothHorizontalResidueConic D
      (-LaurentPolynomial.C (residue R W.a₁) * LaurentPolynomial.T 1) := by
  rw [(smoothHorizontalSecondOutputResidue_action D d hk0 hk hπ).1,
    smoothHorizontalSecondResidue_scale]

end FLT.Mazur.WeierstrassIntegralChart
