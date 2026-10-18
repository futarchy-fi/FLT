/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainIteration
public import FLT.Mazur.WeierstrassDividedFifthInitialResidualRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowJointRestriction

/-!
# The actual depth-one seed in uniform retained-chain coordinates

Conjugate the internal edge by inversion at both endpoints. The last node
keeps its oriented chart identification; its smoothing is unchanged.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFifthInitialIncomingEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 1 hj

local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The actual internal edge in inverse-left to right coordinates. -/
def arithmeticOneSeedIncoming (m : ℕ) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (LaurentPolynomial.invert.trans
    (arithmeticFifthInitialIncomingEquiv hπ data H 1 hj u hu m b)).trans LaurentPolynomial.invert

/-- The fifth depth-one packet supplies both retained nodes and the two boundary edges. -/
def arithmeticOneSeedState : State R π 1 where
  initial := arithmeticFifthInitialSmoothing hπ data H 1 hj u hu
  retained := fun m i b ↦ if i = 0 then
    arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m b else τ m
  terminal := arithmeticFifthShallowTerminalSmoothing hπ data H 1 hj u hu
  edgeEquiv := fun e ↦ match e with
    | .initial => arithmeticFifthInitialEquiv hπ data H 1 hj u hu
    | .incoming _ => arithmeticOneSeedIncoming hπ data H hj u hu
    | .closing => arithmeticFifthInitialClosingEquiv hπ data H 1 hj u hu

local notation "S" => arithmeticOneSeedState hπ data H hj u hu

/-- The conjugated incoming edge retains its original arithmetic quotient square. -/
theorem arithmeticOneSeedIncoming_compatible (b : Bool) :
    PolygonArithmeticSimultaneous.CompatibleEquiv
      (fun m ↦ arithmeticOneSeedIncoming hπ data H hj u hu m b) := by
  intro m
  unfold arithmeticOneSeedIncoming
  apply PolygonSmoothing.punctureEquiv_trans_naturality
  · apply PolygonSmoothing.punctureEquiv_trans_naturality
    · exact PolygonSmoothing.punctureEquiv_invert_naturality _
    · exact arithmeticFifthInitialIncomingEquiv_restriction hπ data H 1 hj u hu m b
  · exact PolygonSmoothing.punctureEquiv_invert_naturality _

/-- Every seed smoothing and full edge respects the coefficient restrictions. -/
theorem arithmeticOneSeedState_compatible : (S).Compatible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact arithmeticFifthInitialSmoothing_restriction hπ data H 1 hj u hu
  · intro m i b
    fin_cases i
    · exact arithmeticFifthInitialNeighborSmoothing_restriction hπ data H 1 hj u hu m b
    · exact arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m
  · exact arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 1 hj u hu
  · intro e b
    cases e with
    | initial => exact fun m ↦ arithmeticFifthInitialEquiv_restriction hπ data H 1 hj u hu m b
    | incoming i => exact arithmeticOneSeedIncoming_compatible hπ data H hj u hu b
    | closing =>
      exact fun m ↦ arithmeticFifthInitialClosingEquiv_restriction hπ data H 1 hj u hu m b

/-- All actual seed smoothings retain their top-power annihilators. -/
theorem arithmeticOneSeedState_annihilated : (S).Annihilated := by
  refine ⟨?_, ?_, ?_⟩
  · intro m b
    apply PolygonArithmeticStages.correctionSmoothing_annihilated
    apply PolygonArithmeticStages.correctionSmoothing_annihilated
    exact arithmeticFourthEarlierInput_annihilated hπ data H 1 hj u hu m b
  · intro m i b
    fin_cases i
    · apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      exact arithmeticFourthPrecedingInput_annihilated hπ data H 1 hj u hu m b
    · exact arithmeticTopSmoothing_annihilated data H m
  · intro m
    apply PolygonArithmeticStages.twoBranchCorrectionRebasedSmoothing_annihilated
    apply PolygonArithmeticStages.twoBranchCorrectionRebasedSmoothing_annihilated
    exact arithmeticFourthTerminalInput_annihilated hπ data H 1 hj u hu m

/-- Every complete seed edge is normalized on the fifth layer, after orientation transport. -/
theorem arithmeticOneSeedState_normalized : (S).Normalized B 5 := by
  intro e b
  cases e with
  | initial => exact arithmeticFifthInitialEquiv_fifth hπ data H 1 hj u hu b
  | incoming i =>
    change arithmeticOneSeedIncoming hπ data H hj u hu 5 b = AlgEquiv.refl
    rw [arithmeticOneSeedIncoming, arithmeticFifthInitialIncomingEquiv_fifth]
    ext z : 1
    exact LaurentPolynomial.involutive_invert z
  | closing => exact arithmeticFifthInitialClosingEquiv_fifth hπ data H 1 hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
