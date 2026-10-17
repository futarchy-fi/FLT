/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointResiduals

/-!
# Geometric simultaneous second corrections

The shared node has one normalized two-branch correction. The predecessor
keeps its changed smoothing, and its old orientation is removed explicitly.
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
local notation "V" => arithmeticSecondJointRetainedIntegralField hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H m

/-- The predecessor's exact smoothing, without discarding any higher drift. -/
def arithmeticSecondPrecedingSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m τ (arithmeticSecondPrecedingIntegralField hπ data H j hj u hu b)

/-- The shared retained node is normalized to its unchanged smoothing at every order. -/
def arithmeticSecondJointRetainedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso
      (arithmeticSecondJointRetainedFactor
        hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op ≪≫
    nodeParameterIso _ τ (arithmeticSecondJointRetainedSmoothing_pair hπ data H j hj u hu m b)

local notation "A" => arithmeticSecondJointRetainedIso hπ data H m j hj u hu

/-- The same shared node correction in the original labeled orientation. -/
def arithmeticSecondJointOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ A b ≪≫ O b

/-- The predecessor's whole chart, including its actual changed smoothing. -/
def arithmeticSecondPrecedingIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅
      PolygonSmoothing.chart Q (arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu b) :=
  Scheme.Spec.mapIso
    (arithmeticSecondPrecedingFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Remove the old labeled orientation before applying the predecessor correction. -/
def arithmeticSecondPrecedingOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅
      PolygonSmoothing.chart Q (arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu b) :=
  (O b).symm ≪≫ arithmeticSecondPrecedingIso hπ data H m j hj u hu b

/-- Both full punctures belong to this single normalized shared node. -/
@[reassoc] theorem arithmeticSecondJointRetainedIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (A b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m τ (V b) a)).hom ≫
        punctureOpen τ a := by
  apply punctureFactor_spec_normalized
  exact arithmeticSecondJointRetainedFactor_puncture hπ data H j hj u hu m b a

/-- The predecessor has both full puncture squares, including its opposite higher error. -/
@[reassoc] theorem arithmeticSecondPrecedingIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticSecondPrecedingIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m τ
        (arithmeticSecondPrecedingIntegralField hπ data H j hj u hu b) a)).hom ≫
      punctureOpen (arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu b) a := by
  apply punctureFactor_spec
  exact correctionNodeFactor_puncture R π m τ _ a

/-- The original orientation square for the simultaneous shared correction. -/
@[reassoc] theorem arithmeticSecondJointOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (arithmeticSecondJointOrientedIso hπ data H m j hj u hu b).hom =
      (A b).hom ≫ (O b).hom := by
  simp only [arithmeticSecondJointOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- The predecessor comparison retains its original orientation exactly. -/
@[reassoc] theorem arithmeticSecondPrecedingOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (arithmeticSecondPrecedingOrientedIso hπ data H m j hj u hu b).hom =
      (arithmeticSecondPrecedingIso hπ data H m j hj u hu b).hom := by
  simp only [arithmeticSecondPrecedingOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
