/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondResidualIdentification
public import FLT.Mazur.WeierstrassDividedResidualLiftFirst

/-!
# Second residual corrections on the actual geometric charts

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
local notation "σ" => arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu

/-- The full terminal correction as a geometric change of chart. -/
def arithmeticSecondResidualLiftTerminalIso :
    PolygonSmoothing.chart Q σ ≅
      PolygonSmoothing.chart Q (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticSecondResidualLiftTerminalFactor
        hπ data H j hj u hu m).toRingEquiv.toCommRingCatIso.op).symm

/-- The retained correction acts on its original full smoothing node at every order. -/
def arithmeticSecondResidualLiftRetainedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  Scheme.Spec.mapIso
      (arithmeticSecondResidualLiftRetainedFactor
        hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op ≪≫
    nodeParameterIso _ τ (arithmeticSecondRetainedSmoothing hπ data H j hj u hu m b)

local notation "O" => twistedRetainedOrientation data H m
local notation "A" => arithmeticSecondResidualLiftRetainedIso hπ data H m j hj u hu

/-- Transport both actual retained corrections into their original labeled orientations. -/
def arithmeticSecondResidualLiftOrientedIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  (O b).symm ≪≫ A b ≪≫ O b

local notation "C" => arithmeticSecondResidualLiftOrientedIso hπ data H m j hj u hu

/-- The forward full-chart comparison uses the original branch orientation. -/
@[reassoc] theorem arithmeticSecondResidualLiftOrientedIso_hom (b : Bool) :
    (O b).hom ≫ (C b).hom = (A b).hom ≫ (O b).hom := by
  simp only [arithmeticSecondResidualLiftOrientedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- The inverse full-chart comparison uses the same original branch orientation. -/
@[reassoc] theorem arithmeticSecondResidualLiftOrientedIso_inv (b : Bool) :
    (O b).hom ≫ (C b).inv = (A b).inv ≫ (O b).hom := by
  simp only [arithmeticSecondResidualLiftOrientedIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- At stage two the terminal chart change is the full inverse square-zero correction. -/
theorem arithmeticSecondResidualLiftTerminalIso_second :
    arithmeticSecondResidualLiftTerminalIso hπ data H 2 j hj u hu ≪≫
        nodeParameterIso (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu 2)
          (arithmeticResidualLiftTerminalSmoothing hπ data H 2 j hj u hu)
          (arithmeticSecondResidualLiftSmoothing_second hπ data H j hj u hu) =
      (Scheme.Spec.mapIso (arithmeticSecondResidualTerminalFactor
        hπ data H j hj u hu).toRingEquiv.toCommRingCatIso.op).symm := by
  apply rebasedCorrection_spec
  exact arithmeticSecondResidualLiftTerminalFactor_second hπ data H j hj u hu

/-- Retained normalization preserves the full second-layer geometric factor. -/
theorem arithmeticSecondResidualLiftRetainedIso_second (b : Bool) :
    arithmeticSecondResidualLiftRetainedIso hπ data H 2 j hj u hu b =
      Scheme.Spec.mapIso (arithmeticSecondResidualRetainedFactor
        hπ data H j hj u hu b).toRingEquiv.toCommRingCatIso.op := by
  apply sourceCorrection_spec
  exact arithmeticSecondResidualLiftRetainedFactor_second hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
