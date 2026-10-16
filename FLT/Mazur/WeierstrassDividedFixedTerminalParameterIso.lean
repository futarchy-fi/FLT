/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFixedTerminalReduction
public import FLT.Mazur.LaurentScaledNilpotentReparametrization

/-!
# Both complete terminal parameter changes are isomorphisms

The tangent reductions construct inverses of the actual Laurent parameter
maps at every arithmetic order. These inverses allow exact edge corrections;
they do not assert that two independent chart normalizations already agree.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation WeierstrassModificationX
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
  (u : Rˣ) (hprimitive : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W ha (π ^ 1) π m
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "c" => arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "v" => arithmeticFixedTerminalUnit π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive m
local notation "E" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6
local notation "J" => ideal Q (parameter R π m)
local notation "hJ" => arithmeticParameterIdeal_nilpotent π m
local notation "L" => Q[T;T⁻¹]
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (ha.map (algebraMap R Q))
local notation "v₁" => fixedTerminalPolygonFirstBoundaryUnit data m j hj
  ha hs h2 h3 h4 h6 u hprimitive
local notation "v₂" => fixedTerminalPolygonSecondBoundaryUnit data m j hj ha hs h2 h3 h4 h6

include hprimitive in
/-- The actual first unit reduces to the constructed coefficient times the inverse variable. -/
theorem fixedTerminalFirstUnit_scaled_reduction :
    (v₁ : L) - algebraMap Q L (↑(-(v)⁻¹ * A) : Q) * LaurentPolynomial.T (-1) ∈
      (J).map (algebraMap Q L) := by
  have h := fixedTerminalPolygonFirstBoundaryUnit_add_tangent_mem data m j hj
    ha hs h2 h3 h4 h6 u hprimitive
  convert h using 1
  simp only [Units.val_mul, Units.val_neg, map_mul, map_neg]
  change _ - (-(algebraMap Q L (↑(v)⁻¹ : Q)) *
    algebraMap Q L (algebraMap R Q W.a₁)) * _ = _
  ring

/-- The full original second boundary parameter has a constructed Laurent algebra inverse. -/
def fixedTerminalSecondBoundaryEquiv : L ≃ₐ[Q] L :=
  LaurentScaledNilpotentReparametrization.equiv J hJ A v₂ (by
    change (v₂ : L) - algebraMap Q L (algebraMap R Q W.a₁) *
      LaurentPolynomial.T (-1) ∈ (J).map (algebraMap Q L)
    rw [mul_comm (algebraMap Q L _)]
    exact fixedTerminalPolygonSecondBoundaryUnit_sub_tangent_mem data m j hj
      ha hs h2 h3 h4 h6)

include hprimitive in
/-- The full normalized first boundary parameter also has a constructed inverse. -/
def fixedTerminalFirstBoundaryEquiv : L ≃ₐ[Q] L :=
  LaurentScaledNilpotentReparametrization.equiv J hJ (-(v)⁻¹ * A) v₁
    (fixedTerminalFirstUnit_scaled_reduction data m j hj ha hs h2 h3 h4 h6 u hprimitive)

/-- The second isomorphism evaluates at the entire original terminal parameter. -/
theorem fixedTerminalSecondBoundaryEquiv_toAlgHom :
    (fixedTerminalSecondBoundaryEquiv data m j hj ha hs h2 h3 h4 h6).toAlgHom =
      LaurentUnitPoints.evalUnit v₂ := rfl

include hprimitive in
/-- The first isomorphism retains the full inverse terminal smoothing factor. -/
theorem fixedTerminalFirstBoundaryEquiv_toAlgHom :
    (fixedTerminalFirstBoundaryEquiv data m j hj ha hs h2 h3 h4 h6 u hprimitive).toAlgHom =
      LaurentUnitPoints.evalUnit v₁ := rfl

include hprimitive in
/-- Both actual terminal parameter maps are isomorphisms of the entire branch torus. -/
instance fixedTerminalPolygonBoundaryParameter_isIso (b : Bool) :
    IsIso (fixedTerminalPolygonBoundaryParameter data m j hj
      ha hs h2 h3 h4 h6 u hprimitive b) := by
  cases b
  · change IsIso (Scheme.Spec.mapIso (fixedTerminalSecondBoundaryEquiv data m j hj
      ha hs h2 h3 h4 h6).toRingEquiv.toCommRingCatIso.op).hom
    infer_instance
  · change IsIso (Scheme.Spec.mapIso (fixedTerminalFirstBoundaryEquiv data m j hj
      ha hs h2 h3 h4 h6 u hprimitive).toRingEquiv.toCommRingCatIso.op).hom
    infer_instance

end FLT.Mazur.WeierstrassDividedDepth
