/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlas
public import FLT.Mazur.WeierstrassDividedTwoFiniteTransitions
public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlasIdentification

/-!
# Both complete closing overlaps in the finite depth-two atlas

The same finite last-node factor serves the internal and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticTwoFiniteAtlasChart arithmeticFifthShallowAtlasChart arithmeticTwoFiniteRetainedIso
  arithmeticTwoFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticTwoFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticTwoFiniteState hπ data H hj u hu k) m 2
local notation "t" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticTwoFiniteState hπ data H hj u hu k) m
local notation "K" => arithmeticTwoFiniteOutgoingIso hπ data H k m hj u hu 2
local notation "F" => arithmeticTwoFiniteTerminalIso hπ data H k m hj u hu
/-- Both installed closing overlaps retain the entire finite corrected residual. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained (2 : Fin 3) b) =
      (punctureSpecIso
        ((arithmeticTwoFiniteState hπ data H hj u hu k).edgeEquiv .closing m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticTwoFiniteLast_chart hπ data H k m hj u hu b
  have ht := arithmeticTwoFiniteAtlasCorrection_chart hπ data H k m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticTwoFiniteRetainedIso_closing_assoc, hl]
  change (edgeInversion Q).hom ≫ leftBranchOpen Q
    (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m) ≫
      arithmeticTwoSeedLastChart hπ data H m hj u hu b = _
  rw [arithmeticTwoSeedAtlas_closing]
  simp only [arithmeticTwoFiniteState_closingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticTwoFiniteOutgoingEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticTwoFiniteTerminalIso_puncture hπ data H k m hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]

/-- Both installed finite closing overlaps are standard on every attained quotient. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_closing_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained (2 : Fin 3) b) =
      punctureOpen t b ≫ ι .terminal := by
  rw [arithmeticTwoFiniteAtlas_residual_closing,
    (arithmeticTwoFiniteState_normalized hπ data H hj u hu k m hm) .closing b,
    PolygonArithmeticRetainedChain.edgeBase, punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
