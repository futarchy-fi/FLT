/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteAtlas
public import FLT.Mazur.WeierstrassDividedOneFiniteTransitions
public import FLT.Mazur.WeierstrassDividedOneFiniteAtlasIdentification

/-!
# Both complete closing overlaps in the finite depth-one atlas

The same finite last-node factor serves the internal and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteAtlasChart arithmeticFifthInitialAtlasChart arithmeticOneFiniteRetainedIso
  arithmeticOneFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticOneFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticOneFiniteState hπ data H hj u hu k) m 1
local notation "t" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticOneFiniteState hπ data H hj u hu k) m
local notation "K" => arithmeticOneFiniteOutgoingIso hπ data H k m hj u hu 1
local notation "F" => arithmeticOneFiniteTerminalIso hπ data H k m hj u hu
/-- Both installed closing overlaps retain the entire finite corrected residual. -/
@[reassoc] theorem arithmeticOneFiniteAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained (1 : Fin 2) b) =
      (punctureSpecIso
        ((arithmeticOneFiniteState hπ data H hj u hu k).edgeEquiv .closing m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticOneFiniteLast_chart hπ data H k m hj u hu b
  have ht := arithmeticOneFiniteAtlasCorrection_chart hπ data H k m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticOneFiniteRetainedIso_closing_assoc, hl]
  change (edgeInversion Q).hom ≫ leftBranchOpen Q
    (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m) ≫
      arithmeticOneSeedLastChart hπ data H m hj u hu b = _
  rw [arithmeticOneSeedAtlas_closing]
  simp only [arithmeticOneFiniteState_closingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticOneFiniteOutgoingEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticOneFiniteTerminalIso_puncture hπ data H k m hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]

/-- Both installed finite closing overlaps are standard on every attained quotient. -/
@[reassoc] theorem arithmeticOneFiniteAtlas_closing_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained (1 : Fin 2) b) =
      punctureOpen t b ≫ ι .terminal := by
  rw [arithmeticOneFiniteAtlas_residual_closing,
    (arithmeticOneFiniteState_normalized hπ data H hj u hu k m hm) .closing b,
    PolygonArithmeticRetainedChain.edgeBase, punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
