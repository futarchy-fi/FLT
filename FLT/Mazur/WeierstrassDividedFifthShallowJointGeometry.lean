/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowJointRestriction
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasSystem

/-!
# Full fifth corrections on the actual fourth chart parameters

Every changed node starts on its actual fourth smoothing. The earlier node
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
local notation "s" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m
local notation "O" => twistedRetainedOrientation data H m

/-- The fifth shared node is identified with its unchanged full smoothing. -/
def arithmeticFifthShallowLastIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso
      (arithmeticFifthShallowLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op ≪≫
    nodeParameterIso _ τ (arithmeticFifthShallowLastSmoothing_pair hπ data H j hj u hu m b)

/-- Install the shared fifth factor in the last node's original orientation. -/
def arithmeticFifthShallowLastOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ arithmeticFifthShallowLastIso hπ data H m j hj u hu b ≪≫ O b

/-- The full predecessor changes its actual fourth smoothing to its fifth smoothing. -/
def arithmeticFifthShallowPrecedingIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅
      PolygonSmoothing.chart Q (arithmeticFifthShallowPrecedingSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFifthShallowPrecedingFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The terminal uses the inverse of the full rebased fifth factor. -/
def arithmeticFifthShallowTerminalIso :
    PolygonSmoothing.chart Q t ≅
      PolygonSmoothing.chart Q (arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticFifthShallowTerminalFactor hπ data H j hj u hu
      m).toRingEquiv.toCommRingCatIso.op).symm

/-- Both normalized last punctures come from one complete fifth node. -/
@[reassoc] theorem arithmeticFifthShallowLastIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticFifthShallowLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m τ
        (arithmeticFifthShallowLastIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen τ a := by
  apply punctureFactor_spec_normalized
  exact arithmeticFifthShallowLastFactor_puncture hπ data H j hj u hu m b a

/-- Both predecessor punctures keep the exact old and new scalar drifts. -/
@[reassoc] theorem arithmeticFifthShallowPrecedingIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticFifthShallowPrecedingIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b)
        (arithmeticFifthShallowPrecedingIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticFifthShallowPrecedingSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFifthShallowPrecedingFactor_puncture hπ data H j hj u hu m b a

/-- The last comparison retains its original branch orientation. -/
@[reassoc] theorem arithmeticFifthShallowLastOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (arithmeticFifthShallowLastOrientedIso hπ data H m j hj u hu b).hom =
      (arithmeticFifthShallowLastIso hπ data H m j hj u hu b).hom ≫ (O b).hom := by
  simp only [arithmeticFifthShallowLastOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
