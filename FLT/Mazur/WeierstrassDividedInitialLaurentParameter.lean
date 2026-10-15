/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorSlopeLaurent

/-!
# An explicit inverse Laurent parameter on the original initial tensor boundary

The parameter is the inverse of the actual localized initial incidence
unit. It splits branch evaluation on every Laurent function.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S]
  (r : SuccessiveIncidence.Coordinate (algebraMap R S π))
  (hr : r ^ 2 + nodeSlopeLinear (W.map (algebraMap R S))
    (algebraMap R S π) (algebraMap R S e.b3) * r =
    nodeSlopeConstant (W.map (algebraMap R S)) (algebraMap R S (π ^ k))
      (algebraMap R S π) (algebraMap R S e.b4) (algebraMap R S e.b6))
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "t₀" => WeierstrassModificationX.t W (π ^ k) d.b3 d.b4 d.b6
local notation "v₀" => WeierstrassModificationX.v W (π ^ k) d.b3 d.b4 d.b6
local notation "A" => PrincipalOpenTensor.transition S x t₀
  (WeierstrassModificationX.overlapEquiv W (π ^ k) d.b3 d.b4 d.b6)
local notation "L" => initialDividedSlopeLaurent hπ d e S r hr

local notation "E" => initialTensorSlopeLaurent hπ d e S r hr
local notation "i" => PrincipalOpenTensor.coefficient (R := R) S t₀
local notation "unit" => WeierstrassModificationX.xOpenUnit W (π ^ k) d.b3 d.b4 d.b6

/-- The inverse original initial incidence is the parameter for the whole Laurent edge. -/
def initialTensorLaurentParameter := LaurentUnitPoints.evalUnit (R := S)
  (Units.map (i).toMonoidHom unit)⁻¹

omit [IsDomain R] in
/-- The positive edge generator is the inverse of the original initial incidence unit. -/
theorem initialTensorLaurentParameter_pos :
    initialTensorLaurentParameter d S (LaurentPolynomial.T 1) = i (↑unit⁻¹) := by
  simp only [initialTensorLaurentParameter, LaurentUnitPoints.evalUnit_T, zpow_one]
  rfl

omit [IsDomain R] in
/-- The negative edge generator is the original initial incidence coordinate. -/
theorem initialTensorLaurentParameter_neg :
    initialTensorLaurentParameter d S (LaurentPolynomial.T (-1)) =
      i (algebraMap _ _ t₀) := by
  simp only [initialTensorLaurentParameter, LaurentUnitPoints.evalUnit_T, zpow_neg_one,
    inv_inv, Units.coe_map, WeierstrassModificationX.xOpenUnit_val]
  rfl

/-- Evaluation and the original inverse-incidence parameter are inverse on every edge function. -/
theorem initialTensorLaurentParameter_section :
    (E).comp (initialTensorLaurentParameter d S) = AlgHom.id S S[T;T⁻¹] := by
  apply LaurentUnitPoints.hom_ext
  · change E (initialTensorLaurentParameter d S (LaurentPolynomial.T 1)) = _
    rw [initialTensorLaurentParameter_pos, initialTensorSlopeLaurent_inverse]
    rfl
  · change E (initialTensorLaurentParameter d S (LaurentPolynomial.T (-1))) = _
    rw [initialTensorLaurentParameter_neg, initialTensorSlopeLaurent_t]
    rfl

/-- Every edge function has an explicit lift to the original localized initial tensor chart. -/
theorem initialTensorSlopeLaurent_surjective : Function.Surjective E := by
  intro z
  refine ⟨initialTensorLaurentParameter d S z, ?_⟩
  exact AlgHom.congr_fun (initialTensorLaurentParameter_section hπ d e S r hr) z

end FLT.Mazur.WeierstrassDividedDepth
