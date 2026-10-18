/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthAtlas
public import FLT.Mazur.WeierstrassDividedZeroFifthTransitions
public import FLT.Mazur.WeierstrassDividedZeroFourthAtlasClosing

/-!
# Both complete closing overlaps in the fifth depth-zero atlas

The same fifth last-node factor serves the initial and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFourthAtlasChart arithmeticZeroFifthLastIso
  arithmeticZeroFifthTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFifthAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroFourthAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroFifthLastSmoothing hπ data H 0 hj u hu m
local notation "t" => arithmeticZeroFifthTerminalSmoothing hπ data H 0 hj u hu m
local notation "K" => arithmeticZeroFifthLastEdgeIso hπ data H m 0 hj u hu
local notation "F" => arithmeticZeroFifthTerminalIso hπ data H m 0 hj u hu
/-- Both installed closing overlaps retain the entire fifth corrected residual. -/
@[reassoc] theorem arithmeticZeroFifthAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticZeroFifthClosingEquiv hπ data H 0 hj u hu m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticZeroFifthAtlasCorrection_chart hπ data H m hj u hu
    (.retained ⟨0, by omega⟩ b)
  change (arithmeticZeroFifthLastIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hl
  have ht := arithmeticZeroFifthAtlasCorrection_chart hπ data H m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticZeroFifthLastIso_closing_assoc, hl]
  rw [arithmeticZeroFourthAtlas_residual_closing]
  simp only [arithmeticZeroFifthClosingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticZeroFifthLastEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticZeroFifthTerminalIso_puncture hπ data H m 0 hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]

omit m in
/-- Both complete closing overlaps are standard on the fifth arithmetic layer. -/
@[reassoc] theorem arithmeticZeroFifthAtlas_closing_fifth (b : Bool) :
    (edgeInversion (Quotient R π 5)).hom ≫
        leftBranchOpen (Quotient R π 5)
          (arithmeticZeroFifthLastSmoothing hπ data H 0 hj u hu 5 b) ≫
          arithmeticZeroFifthAtlasChart hπ data H 5 hj u hu (.retained ⟨0, by omega⟩ b) =
      punctureOpen (arithmeticZeroFifthTerminalSmoothing hπ data H 0 hj u hu 5) b ≫
        arithmeticZeroFifthAtlasChart hπ data H 5 hj u hu .terminal := by
  rw [arithmeticZeroFifthAtlas_residual_closing, arithmeticZeroFifthClosingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
