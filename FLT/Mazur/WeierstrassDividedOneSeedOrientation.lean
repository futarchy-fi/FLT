/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneSeedState
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasIncoming
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasClosing

/-!
# Reconcile the depth-one seed with uniform chain punctures

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
  arithmeticFifthInitialNeighborIso arithmeticFifthInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m

/-- The uniform last inclusion retains the full original orientation. -/
def arithmeticOneSeedLastChart (b : Bool) : PolygonSmoothing.chart Q τ ⟶
    simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu :=
  (O b).hom ≫ ι (.retained ⟨1, by omega⟩ b)

local notation "L" => arithmeticOneSeedLastChart hπ data H m hj u hu

instance arithmeticOneSeedLastChart_isOpenImmersion (b : Bool) : IsOpenImmersion (L b) := by
  unfold arithmeticOneSeedLastChart
  infer_instance

/-- The actual incoming edge in the uniform chain convention is the conjugated residual. -/
@[reassoc] theorem arithmeticOneSeedAtlas_incoming (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticOneSeedIncoming hπ data H hj u hu m b)).hom ≫
        rightBranchOpen Q τ ≫ L b := by
  have h := congrArg (fun f ↦ (edgeInversion Q).hom ≫ f)
    (arithmeticFifthInitialAtlas_residual_incoming hπ data H m hj u hu b)
  simpa only [arithmeticOneSeedIncoming, punctureSpecIso_trans, punctureSpecIso_invert,
    Iso.trans_hom, precedingBranch, arithmeticOneSeedLastChart, Category.assoc] using h

/-- The same oriented whole last chart serves the closing edge without a coordinate change. -/
@[reassoc] theorem arithmeticOneSeedAtlas_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q τ ≫ L b =
      (punctureSpecIso (arithmeticFifthInitialClosingEquiv hπ data H 1 hj u hu m b)).hom ≫
        punctureOpen (arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu m) b ≫
          ι .terminal := by
  simpa only [arithmeticOneSeedLastChart, arithmeticClosingRetainedBoundary, Category.assoc]
    using arithmeticFifthInitialAtlas_residual_closing hπ data H m hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
