/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFiniteAtlas
public import FLT.Mazur.WeierstrassDividedZeroFiniteTransitions
public import FLT.Mazur.WeierstrassDividedZeroFifthAtlasClosing

/-!
# Both complete closing overlaps in the finite depth-zero atlas

The same finite last-node factor serves the initial and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasChart arithmeticZeroFifthAtlasChart arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticZeroFifthAtlasChart hπ data H m hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last
  (arithmeticZeroFiniteState hπ data H 0 hj u hu k) m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal
  (arithmeticZeroFiniteState hπ data H 0 hj u hu k) m
local notation "K" => arithmeticZeroFiniteLastEdgeIso hπ data H k m 0 hj u hu
local notation "F" => arithmeticZeroFiniteTerminalIso hπ data H k m 0 hj u hu
/-- Both installed closing overlaps retain the entire finite corrected residual. -/
@[reassoc] theorem arithmeticZeroFiniteAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).closingEquiv m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticZeroFiniteAtlasCorrection_chart hπ data H k m hj u hu
    (.retained ⟨0, by omega⟩ b)
  change (arithmeticZeroFiniteLastIso hπ data H k m 0 hj u hu b).hom ≫ _ = _ at hl
  have ht := arithmeticZeroFiniteAtlasCorrection_chart hπ data H k m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticZeroFiniteLastIso_closing_assoc, hl]
  rw [arithmeticZeroFifthAtlas_residual_closing]
  simp only [arithmeticZeroFiniteState_closingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticZeroFiniteLastEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticZeroFiniteTerminalIso_puncture hπ data H k m 0 hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]

/-- Both installed finite closing overlaps are standard on every attained quotient. -/
@[reassoc] theorem arithmeticZeroFiniteAtlas_closing_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      punctureOpen t b ≫ ι .terminal := by
  rw [arithmeticZeroFiniteAtlas_residual_closing,
    (arithmeticZeroFiniteState_normalized_le hπ data H 0 hj u hu k m hm).2 b,
    punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
