/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthAtlas
public import FLT.Mazur.WeierstrassDividedZeroFourthTransitions
public import FLT.Mazur.WeierstrassDividedZeroThirdAtlasClosing

/-!
# Both complete closing overlaps in the fourth depth-zero atlas

The same fourth last-node factor serves the initial and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFourthAtlasChart arithmeticZeroThirdAtlasChart arithmeticZeroFourthLastIso
  arithmeticZeroFourthTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFourthAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroThirdAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroFourthLastSmoothing hπ data H 0 hj u hu m
local notation "t" => arithmeticZeroFourthTerminalSmoothing hπ data H 0 hj u hu m
local notation "K" => arithmeticZeroFourthLastEdgeIso hπ data H m 0 hj u hu
local notation "F" => arithmeticZeroFourthTerminalIso hπ data H m 0 hj u hu
/-- Both installed closing overlaps retain the entire fourth corrected residual. -/
@[reassoc] theorem arithmeticZeroFourthAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticZeroFourthClosingEquiv hπ data H 0 hj u hu m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticZeroFourthAtlasCorrection_chart hπ data H m hj u hu
    (.retained ⟨0, by omega⟩ b)
  change (arithmeticZeroFourthLastIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hl
  have ht := arithmeticZeroFourthAtlasCorrection_chart hπ data H m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticZeroFourthLastIso_closing_assoc, hl]
  rw [arithmeticZeroThirdAtlas_residual_closing]
  simp only [arithmeticZeroFourthClosingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticZeroFourthLastEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticZeroFourthTerminalIso_puncture hπ data H m 0 hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]

omit m in
/-- Both complete closing overlaps are standard on the fourth arithmetic layer. -/
@[reassoc] theorem arithmeticZeroFourthAtlas_closing_fourth (b : Bool) :
    (edgeInversion (Quotient R π 4)).hom ≫
        leftBranchOpen (Quotient R π 4)
          (arithmeticZeroFourthLastSmoothing hπ data H 0 hj u hu 4 b) ≫
          arithmeticZeroFourthAtlasChart hπ data H 4 hj u hu (.retained ⟨0, by omega⟩ b) =
      punctureOpen (arithmeticZeroFourthTerminalSmoothing hπ data H 0 hj u hu 4) b ≫
        arithmeticZeroFourthAtlasChart hπ data H 4 hj u hu .terminal := by
  rw [arithmeticZeroFourthAtlas_residual_closing, arithmeticZeroFourthClosingEquiv_fourth,
    punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
