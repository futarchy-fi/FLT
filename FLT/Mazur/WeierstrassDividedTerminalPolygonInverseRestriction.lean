/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalPolygonBoundaryIso
public import FLT.Mazur.WeierstrassDividedTerminalPolygonBoundaryRestriction

/-!
# Inverse terminal parameter changes commute with arithmetic restriction

The inverse is defined on the whole original Laurent torus. It follows the
same coefficient maps, allowing exact reparameterization of endpoint equations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] arithmeticTerminalSmoothing arithmeticCoherentTerminalUnit
  coherentTerminalPolygonIso terminalArithmeticNodeEvaluation terminalPolygonBoundaryParameter
variable (R : Type) [CommRing R] (π : R) (m : ℕ)
local notation "F" => Spec.map (CommRingCat.ofHom
  (PolygonScalingNaturality.coeffMap (AlgHom.toRingHom (restriction R π m))))
local notation "P" => Spec.map (CommRingCat.ofHom
  (ringMap (AlgHom.toRingHom (restriction R π m))
    (parameter R π (m + 1)) (parameter R π m) (restriction_parameter R π m)))
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)

variable [IsDomain R] (hπ : π ≠ 0)
  {W : WeierstrassCurve R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
  (u : Rˣ) (hprimitive : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
include hπ
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "T" => fun a ↦ terminalPolygonBoundaryParameter data a j hj
  ha hs h2 h3 h4 h6 u hprimitive
local notation "E" => fun a b ↦ Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (terminalArithmeticNodeEvaluation data a j hj ha hs h2 h3 h4 h6 b)))
local notation "I" => fun a ↦ coherentTerminalPolygonIso π W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h3 h4 h6 u hprimitive a

local notation "J" => fun a ↦ terminalPolygonBoundaryIso data a j hj
  ha hs h2 h3 h4 h6 u hprimitive

/-- Inverse full terminal parameters commute with the original quotient map. -/
@[reassoc] theorem terminalPolygonBoundaryIso_inv_restriction (opposite : Bool) :
    F ≫ (J (m + 1) opposite).inv = (J m opposite).inv ≫ F := by
  apply (cancel_mono (J (m + 1) opposite).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
  change F = (J m opposite).inv ≫ F ≫ T (m + 1) opposite
  rw [terminalPolygonBoundaryParameter_restriction R π m hπ]
  exact ((J m opposite).inv_hom_id_assoc F).symm

/-- Reparameterizing both orders by their inverses preserves every original Laurent function. -/
@[reassoc] theorem terminalPolygonBoundaryIso_inv_restriction_hom (opposite : Bool) :
    (J m opposite).inv ≫ F ≫ (J (m + 1) opposite).hom = F := by
  change (J m opposite).inv ≫ F ≫ T (m + 1) opposite = F
  rw [terminalPolygonBoundaryParameter_restriction R π m hπ]
  exact (J m opposite).inv_hom_id_assoc F

end FLT.Mazur.WeierstrassDividedDepth
