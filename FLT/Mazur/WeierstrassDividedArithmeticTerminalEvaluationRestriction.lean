/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeBoundary
public import FLT.Mazur.WeierstrassDilatationArithmeticTensorNormalization
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTerminalLaurentRestriction

/-!
# Full normalized terminal evaluations commute with arithmetic restriction

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
local notation "e₀" => WeierstrassDilatation.arithmeticTerminalNodeEquiv π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "e₁" => WeierstrassDilatation.arithmeticTerminalNodeEquiv π (m + 1) W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "v₀" => arithmeticBranchSlope π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "hv₀" => arithmeticBranchSlope_equation π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "v₁" => arithmeticBranchSlope π (m + 1) W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "hv₁" => arithmeticBranchSlope_equation π (m + 1) W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "G₀" => tensorTerminalLaurent W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q₀ v₀ hv₀
local notation "G₁" => tensorTerminalLaurent W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q₁ v₁ hv₁

/-- The two full corrected node evaluations retain the original Laurent coefficient map. -/
theorem terminalArithmeticNodeEvaluation_restriction :
    (PolygonScalingNaturality.coeffMap f).comp (E₁).toRingHom =
      (E₀).toRingHom.comp N := by
  apply RingHom.ext
  intro z
  change PolygonScalingNaturality.coeffMap f (G₁ ((e₁).symm z)) =
    G₀ ((e₀).symm (N z))
  have hg := DFunLike.congr_fun
    (arithmeticTerminalLaurent_restriction R π m W (start + j)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite) ((e₁).symm z)
  have hn := DFunLike.congr_fun
    (WeierstrassDilatation.arithmeticTerminalNodeEquiv_symm_restriction R π m W s
      (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6) z
  exact hg.trans (congrArg G₀ hn)

/-- The original Laurent and full node coefficient projections form a scheme square. -/
@[reassoc] theorem terminalArithmeticNodeEvaluation_restriction_square :
    Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap f)) ≫
      Spec.map (CommRingCat.ofHom (E₁).toRingHom) =
    Spec.map (CommRingCat.ofHom (E₀).toRingHom) ≫ Spec.map (CommRingCat.ofHom N) := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g))
    (terminalArithmeticNodeEvaluation_restriction data m j hj ha hs h2 h3 h4 h6 opposite)

end FLT.Mazur.WeierstrassDividedDepth
