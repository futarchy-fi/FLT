/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedCorrectionBase
public import FLT.Mazur.WeierstrassDividedOriginalNodeBase
public import FLT.Mazur.WeierstrassDividedRevisedLabeledMaps

/-!
# Base compatibility of the complete original terminal comparison

The common terminal map keeps the original normalization, the actual changed
smoothing, and the entire first-order residual correction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π 1 W
  (π ^ (1 + (j + 1))) (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1))
  H.a2_div (H.b4_div _) (H.b6_div _)

omit [IsBezout R] in
/-- The actual common terminal atlas isomorphism preserves its original coefficient ring. -/
@[reassoc] theorem arithmeticFirstResidualAtlasIso_terminal_base :
    (arithmeticFirstResidualAtlasIso hπ data H j hj u hu .terminal).hom ≫
      chartStructure Q σ =
        Spec.map (CommRingCat.ofHom (algebraMap Q (NodalFiber.Coordinate c))) := by
  simp only [arithmeticFirstResidualAtlasIso, changedArithmeticAtlasIso,
    changedArithmeticAtlasToTwisted, arithmeticFirstResidualAtlasCorrection,
    Iso.trans_hom, Iso.symm_symm_eq, Category.assoc]
  rw [arithmeticFirstResidualTerminalIso_base, arithmeticTerminalChangedIso_base]
  dsimp only [twistedArithmeticAtlasIso]
  exact WeierstrassDilatation.fixedTerminalPolygonIso_structure ..

/-- The full terminal comparison agrees with the actual original stage projection. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedTerminal_base :
    arithmeticFirstOriginalRevisedChart hπ data H j hj u hu .terminal ≫
      arithmeticRevisedPolygonToBase data H 1 j hj u hu =
        arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj .terminal ≫
          finiteGlobalArithmeticStructure hπ data (j + 1) hj 1 := by
  change ((arithmeticFirstResidualAtlasIso hπ data H j hj u hu .terminal).hom ≫
    arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu) ≫ _ =
      arithmeticLabeledTerminalChart hπ data H 1 (j + 1) hj ≫ _
  rw [Category.assoc, arithmeticRevisedPolygonTerminalChart_base,
    arithmeticFirstResidualAtlasIso_terminal_base, arithmeticLabeledTerminalChart_base]

end FLT.Mazur.WeierstrassDividedDepth
