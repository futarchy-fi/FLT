/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlas
public import FLT.Mazur.WeierstrassDividedThreeFiniteTransitions
public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlasIdentification

/-!
# Both complete closing overlaps in the finite depth-three atlas

The same finite last-node factor serves the internal and closing edges.
Both closing branches use the one corrected common terminal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThreeFiniteAtlasChart arithmeticThreeSeedAtlasChart arithmeticThreeFiniteRetainedIso
  arithmeticThreeFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticThreeFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticThreeSeedAtlasChart hπ data H m hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticThreeFiniteState hπ data H hj u hu k) m 3
local notation "t" => PolygonArithmeticRetainedChain.State.terminal
  (arithmeticThreeFiniteState hπ data H hj u hu k) m
local notation "K" => arithmeticThreeFiniteOutgoingIso hπ data H k m hj u hu 3
local notation "F" => arithmeticThreeFiniteTerminalIso hπ data H k m hj u hu
/-- Both installed closing overlaps retain the entire finite corrected residual. -/
@[reassoc] theorem arithmeticThreeFiniteAtlas_residual_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained (3 : Fin 4) b) =
      (punctureSpecIso
        ((arithmeticThreeFiniteState hπ data H hj u hu k).edgeEquiv .closing m b)).hom ≫
        punctureOpen t b ≫ ι .terminal := by
  have hl := arithmeticThreeFiniteRetained_chart hπ data H k m hj u hu 3 b
  have ht := arithmeticThreeFiniteAtlasCorrection_chart hπ data H k m hj u hu .terminal
  change (F).hom ≫ _ = _ at ht
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticThreeFiniteRetainedIso_closing_assoc, hl]
  rw [arithmeticThreeSeedAtlas_closing]
  simp only [arithmeticThreeFiniteState_closingEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    arithmeticThreeFiniteOutgoingEquiv_spec, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hT := arithmeticThreeFiniteTerminalIso_puncture hπ data H k m hj u hu b
  simp only [punctureSpecIso_symm, Iso.symm_hom] at hT
  rw [← Category.assoc _ (punctureOpen t b), ← hT, Category.assoc, ht]
  rfl

/-- Both installed finite closing overlaps are standard on every attained quotient. -/
@[reassoc] theorem arithmeticThreeFiniteAtlas_closing_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s b) ≫ ι (.retained (3 : Fin 4) b) =
      punctureOpen t b ≫ ι .terminal := by
  rw [arithmeticThreeFiniteAtlas_residual_closing,
    (arithmeticThreeFiniteState_normalized hπ data H hj u hu k m hm) .closing b,
    PolygonArithmeticRetainedChain.edgeBase, punctureSpecIso_refl, Iso.refl_hom, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
