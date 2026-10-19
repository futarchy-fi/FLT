/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInitialAtlasTransport
public import FLT.Mazur.WeierstrassDividedRevisedInitialMaps

/-!
# Full factor-ratio maps from the corrected diagonal initial opens

Transport the original polynomial factor ratio through the whole accumulated
node isomorphism. The domain is the actual finite pullback open; the two target
nodes retain their separate smoothings. Compatibility with other labels is separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "D" => arithmeticOneDiagonalState hπ data H hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.initial D m

local notation "E" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "T" => arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu

/-- The original full factor ratio is carried to the actual corrected initial open and node. -/
def arithmeticOneDiagonalInitialFactorRatio (b : Bool) :
    arithmeticOneFiniteInitialObject hπ data H m m hj u hu b ⟶
      PolygonSmoothing.chart Q (s b) :=
  (E b).inv ≫ N ≫ (T b).hom

local notation "F" => arithmeticOneDiagonalInitialFactorRatio hπ data H m hj u hu

instance arithmeticOneDiagonalInitialFactorRatio_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticOneDiagonalInitialFactorRatio
  infer_instance

/-- The whole original initial open recovers its full factor-ratio map. -/
@[reassoc] theorem arithmeticOneDiagonalInitialFactorRatio_transport (b : Bool) :
    (E b).hom ≫ F b = N ≫ (T b).hom := by
  rw [arithmeticOneDiagonalInitialFactorRatio, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
