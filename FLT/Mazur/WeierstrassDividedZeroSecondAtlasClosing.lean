/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondAtlas
public import FLT.Mazur.WeierstrassDividedZeroSecondTransitions
public import FLT.Mazur.WeierstrassDividedZeroFirstAtlasClosing

/-!
# Both complete closing overlaps in the second depth-zero atlas

The same second last-node factor serves the initial and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroSecondAtlasChart arithmeticZeroFirstAtlasChart arithmeticZeroSecondLastIso
  arithmeticZeroSecondTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroSecondAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroSecondLastSmoothing hπ data H 0 hj u hu m
local notation "t" => arithmeticZeroSecondTerminalSmoothing hπ data H 0 hj u hu m
local notation "K" => arithmeticZeroSecondLastEdgeIso hπ data H m 0 hj u hu
local notation "F" => arithmeticZeroSecondTerminalIso hπ data H m 0 hj u hu
/-- Both installed closing overlaps retain the entire second corrected residual. -/
@[reassoc] theorem arithmeticZeroSecondAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticZeroSecondClosingEquiv hπ data H 0 hj u hu m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticZeroSecondAtlasCorrection_chart hπ data H m hj u hu
    (.retained ⟨0, by omega⟩ b)
  change (arithmeticZeroSecondLastIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hl
  have ht := arithmeticZeroSecondAtlasCorrection_chart hπ data H m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticZeroSecondLastIso_closing_assoc, hl]
  rw [arithmeticZeroFirstAtlas_residual_closing]
  simp only [arithmeticZeroSecondClosingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticZeroSecondLastEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticZeroSecondTerminalIso_puncture hπ data H m 0 hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]

omit m in
/-- Both complete closing overlaps are standard on the second arithmetic layer. -/
@[reassoc] theorem arithmeticZeroSecondAtlas_closing_second (b : Bool) :
    (edgeInversion (Quotient R π 2)).hom ≫
        leftBranchOpen (Quotient R π 2)
          (arithmeticZeroSecondLastSmoothing hπ data H 0 hj u hu 2 b) ≫
          arithmeticZeroSecondAtlasChart hπ data H 2 hj u hu (.retained ⟨0, by omega⟩ b) =
      punctureOpen (arithmeticZeroSecondTerminalSmoothing hπ data H 0 hj u hu 2) b ≫
        arithmeticZeroSecondAtlasChart hπ data H 2 hj u hu .terminal := by
  rw [arithmeticZeroSecondAtlas_residual_closing, arithmeticZeroSecondClosingEquiv_second,
    punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
