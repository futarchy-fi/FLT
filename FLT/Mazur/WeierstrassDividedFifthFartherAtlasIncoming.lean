/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodeIdentification
public import FLT.Mazur.WeierstrassDividedFifthFartherIdentification
public import FLT.Mazur.WeierstrassDividedFifthFartherIncomingCancellation
public import FLT.Mazur.WeierstrassDividedFourthOuterAtlasIncoming

/-!
# The actual outer incoming overlap in the full fifth depth-three atlas

The outer and farther nodes use their same whole factors on adjacent edges.
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
  (ha : 3 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "s" => arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFifthDeepSmoothing hπ data H j hj u hu FifthDeepNode.outer m
local notation "s₄" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "t₄" => arithmeticFifthDeepInput hπ data H j hj u hu FifthDeepNode.outer m
local notation "P" => arithmeticFifthFartherNeighborIntegralField hπ data H j hj u hu
local notation "M" => arithmeticFourthFartherIdentification hπ data H m j hj u hu 0 ha
local notation "N" => arithmeticFifthFartherInputIdentification
  hπ data H m j hj u hu (by omega) FifthDeepNode.outer 1 ha
local notation "M₅" => arithmeticFifthFartherNeighborIdentification hπ data H m j hj u hu ha
local notation "N₅" => arithmeticFifthFartherNodeIdentification
  hπ data H m j hj u hu ha FifthDeepNode.outer (fun h ↦ FifthDeepNode.noConfusion h) 1 ha

/-- The actual full global outer incoming overlap has the residual from both installed factors. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_residual_outerIncoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M₅ b).hom ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthFartherIncomingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q (t b) ≫ (N₅ b).hom ≫ ι (.retained ⟨1, by omega⟩ b) := by
  have hP := arithmeticFifthFartherNeighborIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at hP
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₄ b) (P b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₄ b) ≫ (M b).hom ≫ κ (.retained ⟨0, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)), ← hP, Category.assoc,
        arithmeticFifthFartherNeighbor_chart]
    _ = (punctureSpecIso
          (arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q (t₄ b) ≫ (N b).hom ≫ κ (.retained ⟨1, by omega⟩ b) := by
      rw [arithmeticFourthOuterIncomingEquiv_spec]
      exact arithmeticFourthOuterAtlas_residual_incoming hπ data H m j hj u hu 0 ha b
    _ = _ := by
      simp only [arithmeticFifthFartherIncomingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm,
        Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
      have hK := arithmeticFifthDeepEdgeEquiv_spec hπ data H j hj u hu m .outer b
      dsimp only [fifthDeepOutgoing, fifthDeepIncoming] at hK
      rw [hK, ← arithmeticFifthDeepNodeIso_incoming_assoc, arithmeticFifthFartherNode_chart]

omit m in
/-- Both installed outer incoming overlaps have identity residual on the fifth layer. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_outerIncoming_fifth (b : Bool) :
    leftBranchOpen (Quotient R π 5)
        (arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu 5 b) ≫
      (arithmeticFifthFartherNeighborIdentification hπ data H 5 j hj u hu ha b).hom ≫
        arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha (.retained ⟨0, by omega⟩ b) =
      precedingBranch (Quotient R π 5)
          (arithmeticFifthDeepSmoothing hπ data H j hj u hu .outer 5 b) ≫
        (arithmeticFifthFartherNodeIdentification hπ data H 5 j hj u hu ha .outer
          (fun h ↦ FifthDeepNode.noConfusion h) 1 ha b).hom ≫
          arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha
            (.retained ⟨1, by omega⟩ b) := by
  rw [arithmeticFifthFartherAtlas_residual_outerIncoming, arithmeticFifthFartherIncomingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
