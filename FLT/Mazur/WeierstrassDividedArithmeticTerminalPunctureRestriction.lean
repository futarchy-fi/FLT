/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalEvaluationRestriction
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureIso
public import FLT.Mazur.NodalFiberPunctureCoefficientMap

/-!
# The full terminal puncture isomorphisms commute with quotient restriction

Both constructed Boolean boundary maps retain every original Laurent function
and every corrected node coordinate across consecutive quotient orders.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) (opposite : Bool)
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "c₀" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "c₁" => WeierstrassDilatation.arithmeticTerminalSmoothing π (m + 1) W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "hc" => WeierstrassDilatation.arithmeticTerminalSmoothing_restriction
  R π m W s (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "N" => NodalFiber.coefficientRingMap f c₁ c₀ hc
local notation "E₀" => terminalArithmeticNodeEvaluation data m j hj ha hs h2 h3 h4 h6 opposite
local notation "E₁" => terminalArithmeticNodeEvaluation data (m + 1) j hj
  ha hs h2 h3 h4 h6 opposite
local notation "δ₀" => ite (opposite = true) (NodalFiber.p c₀) (NodalFiber.q c₀)
local notation "δ₁" => ite (opposite = true) (NodalFiber.p c₁) (NodalFiber.q c₁)
local notation "L₀" => Localization.Away δ₀
local notation "L₁" => Localization.Away δ₁
local notation "i₀" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c₀) L₀))
local notation "i₁" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c₁) L₁))
local notation "P" => Spec.map (CommRingCat.ofHom
  (NodalFiber.punctureCoefficientRingMap f c₁ c₀ hc opposite))
local notation "F" => Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f))
local notation "a₀" => terminalArithmeticPunctureIso data m j hj ha hs h2 h3 h4 h6 opposite
local notation "a₁" => terminalArithmeticPunctureIso data (m + 1) j hj
  ha hs h2 h3 h4 h6 opposite

/-- The actual full puncture isomorphisms retain the original Laurent coefficient map. -/
@[reassoc] theorem terminalArithmeticPunctureIso_restriction :
    F ≫ (a₁).hom = (a₀).hom ≫ P := by
  let _ : IsOpenImmersion i₁ := IsOpenImmersion.of_isLocalization δ₁
  apply (cancel_mono i₁).mp
  rw [Category.assoc, terminalArithmeticPunctureIso_boundary,
    Category.assoc, NodalFiber.punctureCoefficientRingMap_square,
    ← Category.assoc, terminalArithmeticPunctureIso_boundary]
  exact terminalArithmeticNodeEvaluation_restriction_square
    data m j hj ha hs h2 h3 h4 h6 opposite

/-- The inverse puncture comparisons retain the same original coefficient projection. -/
@[reassoc] theorem terminalArithmeticPunctureIso_inv_restriction :
    P ≫ (a₁).inv = (a₀).inv ≫ F := by
  have h := terminalArithmeticPunctureIso_restriction data m j hj ha hs h2 h3 h4 h6 opposite
  have he := congrArg (fun g ↦ (a₀).inv ≫ g ≫ (a₁).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using he.symm

end FLT.Mazur.WeierstrassDividedDepth
