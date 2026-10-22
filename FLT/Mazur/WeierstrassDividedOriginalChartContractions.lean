/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialFormulaCoordinates
public import FLT.Mazur.WeierstrassDividedTerminalLowerCoordinates
public import FLT.Mazur.WeierstrassModificationXUnitIncidence

/-!
# Open cubic contractions for the unchanged atlas charts

Infinity is unchanged at every depth. At start zero the retained initial
chart is an original principal open, and the stage-zero terminal chart is
the original affine chart. These are scheme statements over the full base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R}

/-- A unit scale makes the entire horizontal equation chart an original cubic open. -/
theorem modificationX_toCurve_open_of_unit (u : Rˣ) (b3 b4 b6 : R)
    (h3 : W.a₃ = ↑u * b3) (h4 : W.a₄ = ↑u * b4) (h6 : W.a₆ = (↑u : R) ^ 2 * b6) :
    IsOpenImmersion (WeierstrassModificationX.toCurve W (↑u) b3 b4 b6 h3 h4 h6) := by
  let e := IsLocalization.atUnit _ (S := WeierstrassModificationX.XOpen W (↑u) b3 b4 b6)
    (WeierstrassModificationX.t W (↑u) b3 b4 b6)
    (WeierstrassModificationX.t_isUnit_of_scale_isUnit W (↑u) b3 b4 b6 u.isUnit)
  let _ : IsIso (WeierstrassModificationX.xOpenInclusion W (↑u) b3 b4 b6) :=
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).isIso_hom
  let _ := WeierstrassDilatation.toCurve_isOpenImmersion_of_unit W u b3 b4 b6 h3 h4 h6
  have he : WeierstrassModificationX.toCurve W (↑u) b3 b4 b6 h3 h4 h6 =
      inv (WeierstrassModificationX.xOpenInclusion W (↑u) b3 b4 b6) ≫
        (WeierstrassModificationX.overlapIso W (↑u) b3 b4 b6).hom ≫
          WeierstrassModificationX.dividedOpenInclusion W (↑u) b3 b4 b6 ≫
            WeierstrassDilatation.toCurve W (↑u) b3 b4 b6 h3 h4 h6 := by
    rw [WeierstrassModificationX.overlapIso_toCurve, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)

/-- The infinity chart contracts by an open immersion at every finite stage and start depth. -/
instance globalInfinityOriginalContraction_open :
    IsOpenImmersion (globalIntegralAtlasMap hπ data j hj 0 ≫
      finiteGlobalContraction hπ data j hj) := by
  change IsOpenImmersion (finiteInfinityChart hπ data j hj ≫ _)
  rw [finiteInfinityChart_contraction]
  infer_instance

variable (zeroData : (i : Fin (n + 1)) → Data W π (0 + i.val))
local notation "d" => zeroData ⟨0, Nat.zero_lt_succ n⟩
local notation "unit" => (⟨π ^ 0, 1, by simp, by simp⟩ : Rˣ)
local notation "idx" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))

/-- The terminal chart at final stage zero contracts to an actual original affine open. -/
instance globalZeroTerminalOriginalContraction_open :
    IsOpenImmersion (globalIntegralAtlasMap hπ zeroData 0 (Nat.zero_le n) 1 ≫
      finiteGlobalContraction hπ zeroData 0 (Nat.zero_le n)) := by
  change IsOpenImmersion (finiteSecantDividedChart hπ zeroData 0 (Nat.zero_le n) ≫ _)
  rw [finiteSecantDividedChart_contraction]
  exact WeierstrassDilatation.toCurve_isOpenImmersion_of_unit W unit
    (d).b3 (d).b4 (d).b6 (d).factor3 (d).factor4 (d).factor6

/-- Retaining the initial chart preserves its original cubic open immersion at every stage. -/
instance globalInitialOriginalContraction_open :
    IsOpenImmersion (globalIntegralAtlasMap hπ zeroData j hj idx ≫
      finiteGlobalContraction hπ zeroData j hj) := by
  let e := eqToIso (finiteInitialExteriorObject_eq zeroData j hj)
  have he : globalIntegralAtlasMap hπ zeroData j hj idx ≫
      finiteGlobalContraction hπ zeroData j hj = e.hom ≫
        WeierstrassModificationX.toCurve W (π ^ 0) (d).b3 (d).b4 (d).b6
          (d).factor3 (d).factor4 (d).factor6 := by
    rw [← retainedInitialFormulaCoordinates_cubic, retainedInitialFormulaCoordinates]
    change (e.hom ≫ initialFormulaCoordinates d) ≫ toCurve d = _
    rw [Category.assoc, initialFormulaCoordinates_cubic]
  let _ := modificationX_toCurve_open_of_unit unit
    (d).b3 (d).b4 (d).b6 (d).factor3 (d).factor4 (d).factor6
  rw [he]
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
