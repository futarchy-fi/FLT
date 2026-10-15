/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPunctureIso
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeGeometry

/-!
# The complete terminal standard punctures are actual arithmetic atlas intersections

Both labeled standard punctures give the full fiber product with the last
polygon branch, using the original Laurent comparison in the other leg.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6) (opposite : Bool)
local notation "s" => π ^ (start + j + 1)
local notation "hs₂" => dvd_pow_self π (Nat.succ_ne_zero (start + j))
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs₂ h2 h4 h6


local notation "δ" => ite (opposite = true) (NodalFiber.p c) (NodalFiber.q c)
local notation "L" => Localization.Away δ
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate c) L))
local notation "P" => terminalArithmeticPunctureIso data m j hj ha hs h2 h3 h4 h6 opposite
variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)
local notation "C" => arithmeticTensorBranchChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 opposite
local notation "D" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "A" => finiteArithmeticNewestTensorChart hπ data m j hj

/-- Each complete terminal standard puncture is the exact original labeled chart intersection. -/
theorem terminalArithmeticStandardPuncture_isPullback :
    IsPullback i ((P).inv ≫ PolygonSmoothing.leftBranchOpen Q (parameter R π m))
      ((e).hom ≫ D) (C ≫ A) := by
  apply (terminalArithmeticNodeEvaluation_isPullback data m j hj
    ha hs h2 h3 h4 h6 opposite hπ).of_iso P (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (terminalArithmeticPunctureIso_boundary data m j hj ha hs h2 h3 h4 h6 opposite).symm
  · simp
  · simp
  · simp

/-- Both full standard puncture edges commute in the actual global arithmetic stage. -/
@[reassoc] theorem terminalArithmeticStandardPuncture_overlap :
    i ≫ (e).hom ≫ D =
      (P).inv ≫ PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫ C ≫ A :=
  (terminalArithmeticStandardPuncture_isPullback data m j hj ha hs h2 h3 h4 h6 opposite hπ).w

/-- The full original terminal intersection is the fiber product, for either label. -/
def terminalArithmeticStandardPuncturePullbackIso :=
  (terminalArithmeticStandardPuncture_isPullback data m j hj
    ha hs h2 h3 h4 h6 opposite hπ).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
