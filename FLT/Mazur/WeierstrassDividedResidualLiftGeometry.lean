/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualTerminalIdentification
public import FLT.Mazur.WeierstrassDividedResidualRetainedLift
public import FLT.Mazur.WeierstrassDividedFirstResidualOrientation
public import FLT.Mazur.PolygonArithmeticTwoBranchRebase

/-!
# Geometric lifts in the original arithmetic orientations

The retained smoothing is identified with its original value before
conjugation by the labeled orientation. The terminal smoothing keeps both
higher-order drifts. No incoming puncture is asserted to stay fixed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "q" => arithmeticTerminalIntegralField hπ data H j hj u hu

/-- The terminal source keeps its actual common higher-order smoothing. -/
def arithmeticResidualLiftTerminalSmoothing : Q :=
  twoBranchCorrectionRebasedSmoothing R π m σ q

/-- The full terminal correction as a geometric change of chart. -/
def arithmeticResidualLiftTerminalIso :
    PolygonSmoothing.chart Q σ ≅
      PolygonSmoothing.chart Q (arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu) :=
  (Scheme.Spec.mapIso
    (twoBranchCorrectionRebasedFactor R π m σ q).toRingEquiv.toCommRingCatIso.op).symm

/-- The retained correction acts on its original full smoothing node at every order. -/
def arithmeticResidualLiftRetainedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso
      (arithmeticResidualRetainedLift hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op ≪≫
    nodeParameterIso _ τ (arithmeticResidualRetainedLift_smoothing hπ data H j hj u hu m b)

local notation "O" => twistedRetainedOrientation data H m
local notation "A" => arithmeticResidualLiftRetainedIso hπ data H m j hj u hu

/-- Transport both actual retained corrections into their original labeled orientations. -/
def arithmeticResidualLiftOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ A b ≪≫ O b

local notation "C" => arithmeticResidualLiftOrientedIso hπ data H m j hj u hu

/-- The forward full-chart comparison uses the original branch orientation. -/
@[reassoc] theorem arithmeticResidualLiftOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (C b).hom = (A b).hom ≫ (O b).hom := by
  simp only [arithmeticResidualLiftOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- The inverse full-chart comparison uses the same original branch orientation. -/
@[reassoc] theorem arithmeticResidualLiftOrientedIso_inv (b : Bool) :
    (O b).hom ≫ (C b).inv = (A b).inv ≫ (O b).hom := by
  simp only [arithmeticResidualLiftOrientedIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
