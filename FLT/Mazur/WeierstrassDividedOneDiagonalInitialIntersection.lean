/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneDiagonalFactorRatioBoundary
public import FLT.Mazur.WeierstrassDividedOneDiagonalAtlasOverlaps
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledInitialEdge
public import FLT.Mazur.PullbackLeftLegTransport

/-!
# Complete initial intersections in the actual diagonal atlas

The original initial pullback transports through all finite corrections.
Its retained leg keeps the full original Mobius/right substitution.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialAtlasChart arithmeticOneFiniteInitialIso arithmeticOneFiniteRetainedIso
  arithmeticOneFiniteTerminalIso arithmeticOneFiniteAtlasIso
  simultaneousTwistedArithmeticIso arithmeticInitialBaseEquiv
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticOneFiniteAtlasChart hπ data H m m hj u hu
local notation "D" => arithmeticOneFiniteState hπ data H hj u hu m
local notation "s" => PolygonArithmeticRetainedChain.State.retained D m 0
local notation "E" => arithmeticOneFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu
local notation "P" => arithmeticOneFiniteInitialPuncture hπ data H m m hj u hu
local notation "B" => punctureSpecIso (arithmeticInitialBaseEquiv data H m 1 hj)

/-- The full original initial intersection retains its actual finite Laurent base. -/
theorem arithmeticOneDiagonalAtlas_initial_isPullback (b : Bool) :
    IsPullback (P b) ((B).hom ≫ rightBranchOpen Q (s b))
      (ι (.initial b)) (ι (.retained (0 : Fin 2) b)) := by
  let d := data (Fin.mk 0 (Nat.zero_lt_succ n))
  let J := arithmeticInitialNormalizedPunctureIso π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
  let e := J ≪≫ arithmeticOneFiniteInitialTotalPunctureIso hπ data H m hj u hu m b true
  have he := arithmeticOneDiagonalInitialTotalOpenIso_puncture hπ data H m hj u hu b
  dsimp only [arithmeticOneDiagonalInitialTotalOpenIso] at he
  rw [arithmeticOneFiniteInitialTotalOpenIso_atlas] at he
  exact PullbackOneLegTransport.of_left
    (arithmeticLabeledAtlas_initial_edge_isPullback hπ data H m 2 hj (by omega) b)
    e (E (.initial b)) (E (.retained (0 : Fin 2) b)) G
    (by simpa only [e, Iso.trans_hom, Category.assoc] using he)
    (arithmeticOneFiniteAtlasIso_chart hπ data H m m hj u hu (.initial b))
    (arithmeticOneFiniteAtlasIso_chart hπ data H m m hj u hu (.retained (0 : Fin 2) b))
    (by simpa only [Category.assoc] using
      arithmeticOneFiniteAtlas_initial_normalized hπ data H m m hj u hu (by omega) b)

end FLT.Mazur.WeierstrassDividedDepth
