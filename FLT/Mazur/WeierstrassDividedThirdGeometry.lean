/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdJointRestriction
public import FLT.Mazur.WeierstrassDividedSecondAtlasNodeRestriction

/-!
# Full geometric third corrections

The predecessor starts on its changed second smoothing. Only the last and
unchanged earlier nodes use the old labeled orientation. The terminal keeps
all three rounds of drift.
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
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m
local notation "O" => twistedRetainedOrientation data H m

/-- The third shared node is identified with its unchanged full smoothing. -/
def arithmeticThirdLastIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso
      (arithmeticThirdLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op ≪≫
    nodeParameterIso _ τ (arithmeticThirdLastSmoothing_pair hπ data H j hj u hu m b)

/-- Install the shared third factor in the last node's original orientation. -/
def arithmeticThirdLastOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ arithmeticThirdLastIso hπ data H m j hj u hu b ≪≫ O b

/-- The full predecessor changes its actual second smoothing to its third smoothing. -/
def arithmeticThirdPrecedingIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅
      PolygonSmoothing.chart Q (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticThirdPrecedingFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The full earlier retained node changes both coordinates with its positive field. -/
def arithmeticThirdEarlierIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅
      PolygonSmoothing.chart Q (arithmeticThirdEarlierSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticThirdEarlierFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Remove the earlier retained label's orientation before applying its full factor. -/
def arithmeticThirdEarlierOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅
      PolygonSmoothing.chart Q (arithmeticThirdEarlierSmoothing hπ data H j hj u hu m b) :=
  (O b).symm ≪≫ arithmeticThirdEarlierIso hπ data H m j hj u hu b

/-- The terminal uses the inverse of the full rebased third factor. -/
def arithmeticThirdTerminalIso :
    PolygonSmoothing.chart Q t ≅
      PolygonSmoothing.chart Q (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticThirdTerminalFactor hπ data H j hj u hu m).toRingEquiv.toCommRingCatIso.op).symm

/-- Both normalized last punctures come from one complete third node. -/
@[reassoc] theorem arithmeticThirdLastIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticThirdLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m τ
        (arithmeticThirdLastIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen τ a := by
  apply punctureFactor_spec_normalized
  exact arithmeticThirdLastFactor_puncture hπ data H j hj u hu m b a

/-- Both predecessor punctures keep the exact old and new scalar drifts. -/
@[reassoc] theorem arithmeticThirdPrecedingIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticThirdPrecedingIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b)
        (arithmeticThirdPrecedingIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticThirdPrecedingFactor_puncture hπ data H j hj u hu m b a

/-- The earlier factor includes the full opposite compensation. -/
@[reassoc] theorem arithmeticThirdEarlierIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticThirdEarlierIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m τ
        (arithmeticThirdEarlierIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticThirdEarlierSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticThirdEarlierFactor_puncture hπ data H j hj u hu m b a

/-- The last comparison retains its original branch orientation. -/
@[reassoc] theorem arithmeticThirdLastOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (arithmeticThirdLastOrientedIso hπ data H m j hj u hu b).hom =
      (arithmeticThirdLastIso hπ data H m j hj u hu b).hom ≫ (O b).hom := by
  simp only [arithmeticThirdLastOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- The earlier comparison removes its original branch orientation exactly. -/
@[reassoc] theorem arithmeticThirdEarlierOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (arithmeticThirdEarlierOrientedIso hπ data H m j hj u hu b).hom =
      (arithmeticThirdEarlierIso hπ data H m j hj u hu b).hom := by
  simp only [arithmeticThirdEarlierOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
