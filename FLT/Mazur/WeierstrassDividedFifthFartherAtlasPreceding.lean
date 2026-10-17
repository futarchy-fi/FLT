/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodeIdentification
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasPreceding

/-!
# The actual preceding overlap in the full depth-three fifth atlas

The predecessor and outer nodes use their same whole factors on adjacent edges.
Their installed global overlap equals the complete fifth algebra residual.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFifthFartherAtlasChart
  arithmeticFifthDeepNodeIso arithmeticFifthDeepEarlierIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (ha₃ : 3 = j)
  (a : ℕ) (ha : a + 2 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha₃
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "s" => arithmeticFifthDeepSmoothing hπ data H j hj u hu FifthDeepNode.outer m
local notation "t" => arithmeticFifthDeepSmoothing hπ data H j hj u hu FifthDeepNode.predecessor m
local notation "s₄" => arithmeticFifthDeepInput hπ data H j hj u hu FifthDeepNode.outer m
local notation "t₄" => arithmeticFifthDeepInput hπ data H j hj u hu FifthDeepNode.predecessor m
local notation "P" => arithmeticFifthPairedIntegralField hπ data H j hj u hu
  FourthResidualEdge.outerPreceding FourthResidualEdge.outerIncoming
local notation "M" => arithmeticFifthFartherInputIdentification
  hπ data H m j hj u hu (by omega) FifthDeepNode.outer a ha
local notation "N" => arithmeticFifthFartherInputIdentification
  hπ data H m j hj u hu (by omega) FifthDeepNode.predecessor
    (a + 1) (Eq.trans (Nat.add_assoc a 1 1) ha)
local notation "M₅" => arithmeticFifthFartherNodeIdentification hπ data H m j hj u hu ha₃
  FifthDeepNode.outer (fun h ↦ FifthDeepNode.noConfusion h) a ha
local notation "N₅" => arithmeticFifthFartherNodeIdentification
  hπ data H m j hj u hu ha₃ FifthDeepNode.predecessor
  (fun h ↦ FifthDeepNode.noConfusion h) (a + 1) (Eq.trans (Nat.add_assoc a 1 1) ha)

/-- The actual full global preceding overlap has the residual from both installed factors. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_residual_preceding (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M₅ b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthDeepPrecedingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q (t b) ≫ (N₅ b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  have hP := arithmeticFifthDeepNodeIso_puncture hπ data H j hj u hu m .outer b true
  simp only [punctureOpen_true, fifthDeepOutgoing, fifthDeepIncoming] at hP
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₄ b) (P b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₄ b) ≫ (M b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)), ← hP, Category.assoc,
        arithmeticFifthFartherNode_chart]
    _ = (punctureSpecIso
          (arithmeticFourthOuterPrecedingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q (t₄ b) ≫ (N b).hom ≫ κ (.retained ⟨a + 1, by omega⟩ b) := by
      rw [arithmeticFourthOuterPrecedingEquiv_spec]
      exact arithmeticFourthOuterAtlas_residual_preceding hπ data H m j hj u hu a ha b
    _ = _ := by
      simp only [arithmeticFifthDeepPrecedingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm,
        fifthDeepOutgoing, fifthDeepIncoming,
        Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
      have hK := arithmeticFifthDeepEdgeEquiv_spec hπ data H j hj u hu m .predecessor b
      dsimp only [fifthDeepOutgoing, fifthDeepIncoming] at hK
      rw [hK, ← arithmeticFifthDeepNodeIso_incoming_assoc, arithmeticFifthFartherNode_chart]

omit m in
/-- Both installed preceding overlaps have identity residual on the fifth layer. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_preceding_fifth (b : Bool) :
    leftBranchOpen (Quotient R π 5)
        (arithmeticFifthDeepSmoothing hπ data H j hj u hu .outer 5 b) ≫
      (arithmeticFifthFartherNodeIdentification hπ data H 5 j hj u hu ha₃ .outer
        (fun h ↦ FifthDeepNode.noConfusion h) a ha b).hom ≫
        arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha₃ (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 5)
          (arithmeticFifthDeepSmoothing hπ data H j hj u hu .predecessor 5 b) ≫
        (arithmeticFifthFartherNodeIdentification hπ data H 5 j hj u hu ha₃ .predecessor
          (fun h ↦ FifthDeepNode.noConfusion h) (a + 1)
          (Eq.trans (Nat.add_assoc a 1 1) ha) b).hom ≫
          arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha₃
            (.retained ⟨a + 1, by omega⟩ b) := by
  rw [arithmeticFifthFartherAtlas_residual_preceding, arithmeticFifthDeepPrecedingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
