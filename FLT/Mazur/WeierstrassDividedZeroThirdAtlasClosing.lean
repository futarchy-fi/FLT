/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdAtlas
public import FLT.Mazur.WeierstrassDividedZeroThirdTransitions
public import FLT.Mazur.WeierstrassDividedZeroSecondAtlasClosing

/-!
# Both complete closing overlaps in the third depth-zero atlas

The same third last-node factor serves the initial and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroThirdAtlasChart arithmeticZeroSecondAtlasChart arithmeticZeroThirdLastIso
  arithmeticZeroThirdTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroThirdAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroSecondAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroThirdLastSmoothing hπ data H 0 hj u hu m
local notation "t" => arithmeticZeroThirdTerminalSmoothing hπ data H 0 hj u hu m
local notation "K" => arithmeticZeroThirdLastEdgeIso hπ data H m 0 hj u hu
local notation "F" => arithmeticZeroThirdTerminalIso hπ data H m 0 hj u hu
/-- Both installed closing overlaps retain the entire third corrected residual. -/
@[reassoc] theorem arithmeticZeroThirdAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticZeroThirdClosingEquiv hπ data H 0 hj u hu m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticZeroThirdAtlasCorrection_chart hπ data H m hj u hu
    (.retained ⟨0, by omega⟩ b)
  change (arithmeticZeroThirdLastIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hl
  have ht := arithmeticZeroThirdAtlasCorrection_chart hπ data H m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticZeroThirdLastIso_closing_assoc, hl]
  rw [arithmeticZeroSecondAtlas_residual_closing]
  simp only [arithmeticZeroThirdClosingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticZeroThirdLastEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticZeroThirdTerminalIso_puncture hπ data H m 0 hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]

omit m in
/-- Both complete closing overlaps are standard on the third arithmetic layer. -/
@[reassoc] theorem arithmeticZeroThirdAtlas_closing_third (b : Bool) :
    (edgeInversion (Quotient R π 3)).hom ≫
        leftBranchOpen (Quotient R π 3)
          (arithmeticZeroThirdLastSmoothing hπ data H 0 hj u hu 3 b) ≫
          arithmeticZeroThirdAtlasChart hπ data H 3 hj u hu (.retained ⟨0, by omega⟩ b) =
      punctureOpen (arithmeticZeroThirdTerminalSmoothing hπ data H 0 hj u hu 3) b ≫
        arithmeticZeroThirdAtlasChart hπ data H 3 hj u hu .terminal := by
  rw [arithmeticZeroThirdAtlas_residual_closing, arithmeticZeroThirdClosingEquiv_third,
    punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
