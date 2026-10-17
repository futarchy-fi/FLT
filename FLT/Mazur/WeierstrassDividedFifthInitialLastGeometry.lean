/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialLastNodes
public import FLT.Mazur.WeierstrassDividedFifthShallowJointGeometry
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasSystem

/-!
# The depth-one fifth last-node geometry

The last node retains its full smoothing and original labeled orientation.
Its two punctures come from one whole-node factor.
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
local notation "O" => twistedRetainedOrientation data H m

/-- The fifth shared node is identified with its unchanged full smoothing. -/
def arithmeticFifthInitialLastIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso
      (arithmeticFifthInitialLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op ≪≫
    nodeParameterIso _ τ (arithmeticFifthInitialLastSmoothing_pair hπ data H j hj u hu m b)

/-- Install the shared fifth factor in the last node's original orientation. -/
def arithmeticFifthInitialLastOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ arithmeticFifthInitialLastIso hπ data H m j hj u hu b ≪≫ O b

/-- Both normalized last punctures come from one complete fifth node. -/
@[reassoc] theorem arithmeticFifthInitialLastIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticFifthInitialLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m τ
        (arithmeticFifthInitialLastIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen τ a := by
  apply punctureFactor_spec_normalized
  exact arithmeticFifthInitialLastFactor_puncture hπ data H j hj u hu m b a

/-- The last comparison retains its original branch orientation. -/
@[reassoc] theorem arithmeticFifthInitialLastOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (arithmeticFifthInitialLastOrientedIso hπ data H m j hj u hu b).hom =
      (arithmeticFifthInitialLastIso hπ data H m j hj u hu b).hom ≫ (O b).hom := by
  simp only [arithmeticFifthInitialLastOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
