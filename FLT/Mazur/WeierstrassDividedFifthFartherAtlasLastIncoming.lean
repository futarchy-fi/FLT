/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherEndIdentification
public import FLT.Mazur.WeierstrassDividedFifthShallowTransitions
public import FLT.Mazur.WeierstrassDividedFourthAtlasIncoming
public import FLT.Mazur.WeierstrassDividedFifthShallowIncomingCancellation

/-!
# The actual incoming overlap of the depth-three fifth atlas

The last factor is shared with the closing edge. The full predecessor factor
retains the exact fourth and fifth smoothing in the global comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowPrecedingIso arithmeticFifthFartherAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (ha₃ : 3 = j)
  (a : ℕ) (ha : a + 1 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha₃
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" =>
  arithmeticFifthDeepSmoothing hπ data H j hj u hu FifthDeepNode.predecessor m
local notation "s₄" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m
local notation "P" => arithmeticFifthPairedIntegralField hπ data H j hj u hu
  FourthResidualEdge.incoming FourthResidualEdge.outerPreceding
local notation "M" => arithmeticFourthOuterPrecedingIdentification
  hπ data H m j hj u hu a ha (by omega)
local notation "N" => arithmeticFourthOuterLastIdentification hπ data H m j hj u hu

local notation "D" => arithmeticFifthFartherNodeIdentification
  hπ data H m j hj u hu ha₃ FifthDeepNode.predecessor
  (fun h ↦ FifthDeepNode.noConfusion h) a ha
local notation "L₅" => arithmeticFifthFartherLastIdentification hπ data H m j hj u hu

/-- The full fourth incoming residual is retained at the depth-three fifth input labels. -/
@[reassoc] theorem arithmeticFifthFartherInput_residual_incoming (b : Bool) :
    leftBranchOpen Q (s₄ b) ≫ (M b).hom ≫ κ (.retained ⟨a, by omega⟩ b) =
      (arithmeticFourthIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
  have hM : (M b).hom ≫ κ (.retained ⟨a, by omega⟩ b) =
      (arithmeticFourthPrecedingIdentification hπ data H m j hj u hu a ha b).hom ≫
        arithmeticFourthAtlasChart hπ data H m j hj u hu (.retained ⟨a, by omega⟩ b) := by
    apply (cancel_epi (arithmeticFourthPrecedingIso hπ data H m j hj u hu b).hom).mp
    rw [arithmeticFourthOuterPreceding_chart, arithmeticFourthPreceding_chart]
  rw [hM, arithmeticFourthOuterLast_chart_eq, arithmeticFourthInitialLast_chart_eq]
  exact arithmeticFourthAtlas_residual_incoming hπ data H m j hj u hu a ha b

/-- The installed incoming overlap is precisely the complete fifth residual. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_residual_incoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthDeepIncomingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (L₅ b).hom ≫ ι (.retained ⟨j, by omega⟩ b) := by
  have hP := arithmeticFifthDeepNodeIso_puncture hπ data H j hj u hu m .predecessor b true
  simp only [punctureOpen_true, fifthDeepOutgoing, fifthDeepIncoming,
    arithmeticFifthDeepInput] at hP
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₄ b) (P b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₄ b) ≫ (M b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)), ← hP, Category.assoc,
        arithmeticFifthFartherNode_chart]
      rfl
    _ = (arithmeticFourthIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N b).hom ≫ κ (.retained ⟨j, by omega⟩ b) :=
      arithmeticFifthFartherInput_residual_incoming hπ data H m j hj u hu ha₃ a ha b
    _ = _ := by
      simp only [arithmeticFifthDeepIncomingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, fifthDeepOutgoing, fifthDeepIncoming, arithmeticFifthDeepInput,
        arithmeticFifthShallowLastEdgeEquiv_spec,
        arithmeticFourthIncomingEquiv_spec, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFifthShallowLastOrientedIso_incoming_assoc,
        arithmeticFifthFartherLast_chart]

omit m in
/-- Both actual incoming residuals vanish on the fifth layer. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_incoming_fifth (b : Bool) :
    leftBranchOpen (Quotient R π 5)
        (arithmeticFifthDeepSmoothing hπ data H j hj u hu .predecessor 5 b) ≫
      (arithmeticFifthFartherNodeIdentification hπ data H 5 j hj u hu ha₃ .predecessor
        (fun h ↦ FifthDeepNode.noConfusion h) a ha b).hom ≫
        arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha₃ (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 5)
          (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 5) ≫
        (twistedRetainedOrientation data H 5 b).hom ≫
          (arithmeticFifthFartherLastIdentification hπ data H 5 j hj u hu b).hom ≫
          arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha₃
            (.retained ⟨j, by omega⟩ b) := by
  rw [arithmeticFifthFartherAtlas_residual_incoming, arithmeticFifthDeepIncomingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
