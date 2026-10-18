/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlas
public import FLT.Mazur.WeierstrassDividedThreeFiniteAtlasIdentification
public import FLT.Mazur.WeierstrassDividedThreeFiniteTransitions

/-!
# The complete internal overlap in the finite depth-three atlas

Both incident punctures come from the same full retained-node comparisons.
The seed overlap retains its two inversion maps.
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
  (arithmeticThreeFiniteState hπ data H hj u hu k) m
variable (i : Fin 3)
local notation "K" => arithmeticThreeFiniteOutgoingIso hπ data H k m hj u hu i.castSucc

/-- The installed internal overlap is the full finite residual between its actual neighbors. -/
@[reassoc] theorem arithmeticThreeFiniteAtlas_residual_incoming (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s i.castSucc b) ≫ ι (.retained i.castSucc b) =
      (punctureSpecIso
        ((arithmeticThreeFiniteState hπ data H hj u hu k).edgeEquiv (.incoming i) m b)).hom ≫
          rightBranchOpen Q (s i.succ b) ≫ ι (.retained i.succ b) := by
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticThreeFiniteRetainedIso_closing_assoc, arithmeticThreeFiniteRetained_chart]
  rw [arithmeticThreeSeedAtlas_incoming]
  simp only [arithmeticThreeFiniteState_incomingEquiv, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticThreeFiniteOutgoingEquiv_spec, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have h := arithmeticThreeFiniteRetainedIso_puncture hπ data H k m hj u hu i.succ b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s i.succ b)), ← h, Category.assoc,
    arithmeticThreeFiniteRetained_chart]

/-- All three installed internal edges are standard at every attained arithmetic order. -/
@[reassoc] theorem arithmeticThreeFiniteAtlas_incoming_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s i.castSucc b) ≫ ι (.retained i.castSucc b) =
      rightBranchOpen Q (s i.succ b) ≫ ι (.retained i.succ b) := by
  rw [arithmeticThreeFiniteAtlas_residual_incoming,
    (arithmeticThreeFiniteState_normalized hπ data H hj u hu k m hm) (.incoming i) b]
  rw [PolygonArithmeticRetainedChain.edgeBase, punctureSpecIso_refl, Iso.refl_hom,
    Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
