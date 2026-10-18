/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoSeedState
public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasIncoming
public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasClosing
public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasPreceding

/-!
# Reconcile the depth-two seed with uniform chain punctures

The last retained chart includes its original orientation isomorphism.
Precomposing the incoming edge with inversion gives inverse-left to right,
while the closing edge already uses inverse-left to the common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowNeighborIso arithmeticFifthShallowAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticFifthShallowPrecedingSmoothing hπ data H 2 hj u hu m

/-- The uniform last inclusion retains the full original orientation. -/
def arithmeticTwoSeedLastChart (b : Bool) : PolygonSmoothing.chart Q τ ⟶
    simultaneousTwistedArithmeticStage hπ data H m 2 hj u hu :=
  (O b).hom ≫ ι (.retained ⟨2, by omega⟩ b)

local notation "L" => arithmeticTwoSeedLastChart hπ data H m hj u hu

instance arithmeticTwoSeedLastChart_isOpenImmersion (b : Bool) : IsOpenImmersion (L b) := by
  unfold arithmeticTwoSeedLastChart
  infer_instance

/-- The actual incoming edge in the uniform chain convention is the conjugated residual. -/
@[reassoc] theorem arithmeticTwoSeedAtlas_incoming (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨1, by omega⟩ b) =
      (punctureSpecIso (arithmeticTwoSeedIncoming hπ data H hj u hu m 1 b)).hom ≫
        rightBranchOpen Q τ ≫ L b := by
  have h := congrArg (fun f ↦ (edgeInversion Q).hom ≫ f)
    (arithmeticFifthShallowAtlas_residual_incoming hπ data H m hj u hu b)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simpa only [arithmeticTwoSeedIncoming, h10, ↓reduceIte,
    punctureSpecIso_trans, punctureSpecIso_invert,
    Iso.trans_hom, precedingBranch, arithmeticTwoSeedLastChart, Category.assoc] using h

/-- The additional predecessor edge keeps both inversion maps and its full residual. -/
@[reassoc] theorem arithmeticTwoSeedAtlas_preceding (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q
        (arithmeticFifthShallowNeighborSmoothing hπ data H 2 hj u hu m b) ≫
      ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticTwoSeedIncoming hπ data H hj u hu m 0 b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨1, by omega⟩ b) := by
  have h := congrArg (fun f ↦ (edgeInversion Q).hom ≫ f)
    (arithmeticFifthShallowAtlas_residual_preceding hπ data H m hj u hu b)
  simpa only [arithmeticTwoSeedIncoming, Fin.isValue, ↓reduceIte,
    punctureSpecIso_trans, punctureSpecIso_invert,
    Iso.trans_hom, precedingBranch, Category.assoc] using h

/-- The same oriented whole last chart serves the closing edge without a coordinate change. -/
@[reassoc] theorem arithmeticTwoSeedAtlas_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q τ ≫ L b =
      (punctureSpecIso (arithmeticFifthShallowClosingEquiv hπ data H 2 hj u hu m b)).hom ≫
        punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu m) b ≫
          ι .terminal := by
  simpa only [arithmeticTwoSeedLastChart, arithmeticClosingRetainedBoundary, Category.assoc]
    using arithmeticFifthShallowAtlas_residual_closing hπ data H m hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
