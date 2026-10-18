/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlas
public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlasIdentification
public import FLT.Mazur.WeierstrassDividedTwoFiniteTransitions

/-!
# The complete internal overlap in the finite depth-two atlas

Both incident punctures come from the same full retained-node comparisons.
The seed overlap retains its two inversion maps.
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
  (arithmeticTwoFiniteState hπ data H hj u hu k) m
local notation "K" => arithmeticTwoFiniteOutgoingIso hπ data H k m hj u hu 1

/-- The installed internal overlap is the full finite residual between its actual neighbors. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_residual_incoming (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s 1 b) ≫ ι (.retained 1 b) =
      (punctureSpecIso
        ((arithmeticTwoFiniteState hπ data H hj u hu k).edgeEquiv (.incoming 1) m b)).hom ≫
          rightBranchOpen Q (s 2 b) ≫ ι (.retained 2 b) := by
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticTwoFiniteRetainedIso_closing_assoc, arithmeticTwoFiniteMiddle_chart]
  change (edgeInversion Q).hom ≫ leftBranchOpen Q
    (arithmeticFifthShallowPrecedingSmoothing hπ data H 2 hj u hu m b) ≫
      κ (.retained ⟨1, by omega⟩ b) = _
  rw [arithmeticTwoSeedAtlas_incoming]
  have hc : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  have hs : (1 : Fin 2).succ = (2 : Fin 3) := rfl
  simp only [arithmeticTwoFiniteState_incomingEquiv, hc, hs, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticTwoFiniteOutgoingEquiv_spec, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have h := arithmeticTwoFiniteRetainedIso_puncture hπ data H k m hj u hu 2 b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s 2 b)), ← h, Category.assoc,
    arithmeticTwoFiniteLast_chart]
  rfl

/-- Both installed internal edges are standard at every attained arithmetic order. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_incoming_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s 1 b) ≫ ι (.retained 1 b) =
      rightBranchOpen Q (s 2 b) ≫ ι (.retained 2 b) := by
  rw [arithmeticTwoFiniteAtlas_residual_incoming,
    (arithmeticTwoFiniteState_normalized hπ data H hj u hu k m hm) (.incoming 1) b]
  rw [PolygonArithmeticRetainedChain.edgeBase, punctureSpecIso_refl, Iso.refl_hom,
    Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth

/-!
# The complete preceding overlap in the finite depth-two atlas

Both incident punctures come from the same full retained-node comparisons.
The seed overlap retains its two inversion maps.
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
  (arithmeticTwoFiniteState hπ data H hj u hu k) m
local notation "K" => arithmeticTwoFiniteOutgoingIso hπ data H k m hj u hu 0

/-- The installed preceding overlap is the full finite residual between its actual neighbors. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_residual_preceding (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s 0 b) ≫ ι (.retained 0 b) =
      (punctureSpecIso
        ((arithmeticTwoFiniteState hπ data H hj u hu k).edgeEquiv (.incoming 0) m b)).hom ≫
          rightBranchOpen Q (s 1 b) ≫ ι (.retained 1 b) := by
  apply (cancel_epi (K b).hom).mp
  rw [← arithmeticTwoFiniteRetainedIso_closing_assoc, arithmeticTwoFiniteFirst_chart]
  change (edgeInversion Q).hom ≫ leftBranchOpen Q
    (arithmeticFifthShallowNeighborSmoothing hπ data H 2 hj u hu m b) ≫
      κ (.retained ⟨0, by omega⟩ b) = _
  rw [arithmeticTwoSeedAtlas_preceding]
  have hc : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have hs : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  simp only [arithmeticTwoFiniteState_incomingEquiv, hc, hs, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticTwoFiniteOutgoingEquiv_spec, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have h := arithmeticTwoFiniteRetainedIso_puncture hπ data H k m hj u hu 1 b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s 1 b)), ← h, Category.assoc,
    arithmeticTwoFiniteMiddle_chart]
  rfl

/-- Both installed preceding edges are standard at every attained arithmetic order. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_preceding_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q (s 0 b) ≫ ι (.retained 0 b) =
      rightBranchOpen Q (s 1 b) ≫ ι (.retained 1 b) := by
  rw [arithmeticTwoFiniteAtlas_residual_preceding,
    (arithmeticTwoFiniteState_normalized hπ data H hj u hu k m hm) (.incoming 0) b]
  rw [PolygonArithmeticRetainedChain.edgeBase, punctureSpecIso_refl, Iso.refl_hom,
    Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
