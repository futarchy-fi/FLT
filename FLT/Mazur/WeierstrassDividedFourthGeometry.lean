/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthJointRestriction
public import FLT.Mazur.WeierstrassDividedThirdInitialAtlasSystem

/-!
# Full fourth corrections on the actual third chart parameters

Every changed node starts on its actual third smoothing. The earlier node
already has normalized coordinates; only the last uses the labeled orientation.
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
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu m
local notation "O" => twistedRetainedOrientation data H m

/-- The fourth shared node is identified with its unchanged full smoothing. -/
def arithmeticFourthLastIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso
      (arithmeticFourthLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op ≪≫
    nodeParameterIso _ τ (arithmeticFourthLastSmoothing_pair hπ data H j hj u hu m b)

/-- Install the shared fourth factor in the last node's original orientation. -/
def arithmeticFourthLastOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ arithmeticFourthLastIso hπ data H m j hj u hu b ≪≫ O b

/-- The full predecessor changes its actual third smoothing to its fourth smoothing. -/
def arithmeticFourthPrecedingIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅
      PolygonSmoothing.chart Q (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFourthPrecedingFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The earlier node retains its entire previous smoothing and normalized orientation. -/
def arithmeticFourthEarlierIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticFourthEarlierSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFourthEarlierFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The terminal uses the inverse of the full rebased fourth factor. -/
def arithmeticFourthTerminalIso :
    PolygonSmoothing.chart Q t ≅
      PolygonSmoothing.chart Q (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticFourthTerminalFactor hπ data H j hj u hu m).toRingEquiv.toCommRingCatIso.op).symm

/-- Both normalized last punctures come from one complete fourth node. -/
@[reassoc] theorem arithmeticFourthLastIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticFourthLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m τ
        (arithmeticFourthLastIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen τ a := by
  apply punctureFactor_spec_normalized
  exact arithmeticFourthLastFactor_puncture hπ data H j hj u hu m b a

/-- Both predecessor punctures keep the exact old and new scalar drifts. -/
@[reassoc] theorem arithmeticFourthPrecedingIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticFourthPrecedingIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b)
        (arithmeticFourthPrecedingIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFourthPrecedingFactor_puncture hπ data H j hj u hu m b a

/-- The earlier factor includes the full opposite compensation. -/
@[reassoc] theorem arithmeticFourthEarlierIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticFourthEarlierIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b)
        (arithmeticFourthEarlierIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticFourthEarlierSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFourthEarlierFactor_puncture hπ data H j hj u hu m b a

/-- The last comparison retains its original branch orientation. -/
@[reassoc] theorem arithmeticFourthLastOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (arithmeticFourthLastOrientedIso hπ data H m j hj u hu b).hom =
      (arithmeticFourthLastIso hπ data H m j hj u hu b).hom ≫ (O b).hom := by
  simp only [arithmeticFourthLastOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
