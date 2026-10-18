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
# The complete internal overlap in the finite depth-one atlas

Both incident punctures come from the same full retained-node comparisons.
The seed overlap retains its two inversion maps.
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
  (arithmeticOneFiniteState hπ data H hj u hu k) m
local notation "K" => arithmeticOneFiniteOutgoingIso hπ data H k m hj u hu 0

/-- The installed internal overlap is the full finite residual between its actual neighbors. -/
@[reassoc] theorem arithmeticOneFiniteAtlas_residual_incoming (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s 0 b) ≫ ι (.retained 0 b) =
      (punctureSpecIso
        ((arithmeticOneFiniteState hπ data H hj u hu k).edgeEquiv (.incoming 0) m b)).hom ≫
          rightBranchOpen Q (s 1 b) ≫ ι (.retained 1 b) := by
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticOneFiniteRetainedIso_closing_assoc, arithmeticOneFiniteFirst_chart]
  change (edgeInversion Q).hom ≫ leftBranchOpen Q
    (arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m b) ≫
      κ (.retained ⟨0, by omega⟩ b) = _
  rw [arithmeticOneSeedAtlas_incoming]
  simp only [arithmeticOneFiniteState_incomingEquiv, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticOneFiniteOutgoingEquiv_spec, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have h := arithmeticOneFiniteRetainedIso_puncture hπ data H k m hj u hu 1 b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s 1 b)), ← h, Category.assoc,
    arithmeticOneFiniteLast_chart]
  rfl

/-- Both installed internal edges are standard at every attained arithmetic order. -/
@[reassoc] theorem arithmeticOneFiniteAtlas_incoming_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s 0 b) ≫ ι (.retained 0 b) =
      rightBranchOpen Q (s 1 b) ≫ ι (.retained 1 b) := by
  rw [arithmeticOneFiniteAtlas_residual_incoming,
    (arithmeticOneFiniteState_normalized hπ data H hj u hu k m hm) (.incoming 0) b]
  rw [PolygonArithmeticRetainedChain.edgeBase, punctureSpecIso_refl, Iso.refl_hom,
    Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
