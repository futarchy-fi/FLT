/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEndIdentification
public import FLT.Mazur.WeierstrassDividedFourthFartherAdjacent

/-!
# The actual farther incoming overlap in the full fifth deep atlas

The farther and earlier nodes use their same whole factors on adjacent edges.
Their installed global overlap equals the complete fifth algebra residual.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFifthDeepAtlasChart
  arithmeticFifthDeepNodeIso arithmeticFifthDeepEarlierIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (hj₄ : 4 ≤ j)
  (a : ℕ) (ha : a + 4 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "s" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFifthDeepSmoothing hπ data H j hj u hu FifthDeepNode.farther m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "O" => twistedRetainedOrientation data H m
local notation "t₄" => arithmeticFifthDeepInput hπ data H j hj u hu FifthDeepNode.farther m
local notation "P" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu
local notation "M" => arithmeticFifthDeepEarlierInputIdentification hπ data H m j hj u hu a ha
local notation "N" => arithmeticFifthDeepInputIdentification
  hπ data H m j hj u hu hj₄ FifthDeepNode.farther (a + 1) (Eq.trans (Nat.add_assoc a 1 3) ha)
local notation "M₅" => arithmeticFifthDeepEarlierIdentification hπ data H m j hj u hu a ha
local notation "N₅" => arithmeticFifthDeepNodeIdentification
  hπ data H m j hj u hu FifthDeepNode.farther (a + 1) (Eq.trans (Nat.add_assoc a 1 3) ha)

/-- The actual full global farther incoming overlap has the residual from both installed factors. -/
@[reassoc] theorem arithmeticFifthDeepAtlas_residual_fartherIncoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M₅ b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthDeepFartherIncomingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q (t b) ≫ (N₅ b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  have hP := arithmeticFifthDeepEarlierIso_puncture hπ data H j hj u hu m b true
  simp only [punctureOpen_true] at hP
  apply (cancel_epi
    (punctureSpecIso (correctionPunctureFactor R π m τ (P b) true)).hom).mp
  calc
    _ = leftBranchOpen Q τ ≫ (O b).hom ≫ (M b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)), ← hP, Category.assoc,
        arithmeticFifthDeepEarlier_chart]
    _ = (punctureSpecIso
          (arithmeticFourthFartherIncomingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q (t₄ b) ≫ (N b).hom ≫ κ (.retained ⟨a + 1, by omega⟩ b) := by
      rw [arithmeticFourthFartherIncomingEquiv_spec]
      exact arithmeticFourthOuterAtlas_farther_adjacent hπ data H m j hj u hu a ha b
    _ = _ := by
      simp only [arithmeticFifthDeepFartherIncomingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm,
        fifthDeepOutgoing, fifthDeepIncoming,
        Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
      have hK := arithmeticFifthDeepEdgeEquiv_spec hπ data H j hj u hu m .farther b
      dsimp only [fifthDeepOutgoing, fifthDeepIncoming] at hK
      rw [hK, ← arithmeticFifthDeepNodeIso_incoming_assoc, arithmeticFifthDeepNode_chart]

omit m in
/-- Both installed farther incoming overlaps have identity residual on the fifth layer. -/
@[reassoc] theorem arithmeticFifthDeepAtlas_fartherIncoming_fifth (b : Bool) :
    leftBranchOpen (Quotient R π 5)
        (arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu 5 b) ≫
      (arithmeticFifthDeepEarlierIdentification hπ data H 5 j hj u hu a ha b).hom ≫
        arithmeticFifthDeepAtlasChart hπ data H 5 j hj u hu hj₄ (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 5)
          (arithmeticFifthDeepSmoothing hπ data H j hj u hu .farther 5 b) ≫
        (arithmeticFifthDeepNodeIdentification hπ data H 5 j hj u hu .farther (a + 1)
          (Eq.trans (Nat.add_assoc a 1 3) ha) b).hom ≫
          arithmeticFifthDeepAtlasChart hπ data H 5 j hj u hu hj₄
            (.retained ⟨a + 1, by omega⟩ b) := by
  rw [arithmeticFifthDeepAtlas_residual_fartherIncoming,
    arithmeticFifthDeepFartherIncomingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
