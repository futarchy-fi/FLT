/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainIteration
public import FLT.Mazur.WeierstrassDividedFifthShallowRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowJointRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowResidualRestriction

/-!
# The actual depth-two seed in uniform retained-chain coordinates

Conjugate the internal edge by inversion at both endpoints. The last node
keeps its oriented chart identification; its smoothing is unchanged.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFifthShallowIncomingEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 2 hj

local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The actual internal edge in inverse-left to right coordinates. -/
def arithmeticTwoSeedIncoming (m : ℕ) (i : Fin 2) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (LaurentPolynomial.invert.trans
    (if i = 0 then arithmeticFifthShallowPrecedingEquiv hπ data H 2 hj u hu m b
      else arithmeticFifthShallowIncomingEquiv hπ data H 2 hj u hu m b)).trans
        LaurentPolynomial.invert

/-- The fifth depth-two packet supplies three retained nodes and the two boundary edges. -/
def arithmeticTwoSeedState : State R π 2 where
  initial := arithmeticFifthShallowSmoothing hπ data H 2 hj u hu
  retained := fun m i b ↦ if i = 0 then
    arithmeticFifthShallowNeighborSmoothing hπ data H 2 hj u hu m b else if i = 1 then
      arithmeticFifthShallowPrecedingSmoothing hπ data H 2 hj u hu m b else τ m
  terminal := arithmeticFifthShallowTerminalSmoothing hπ data H 2 hj u hu
  edgeEquiv := fun e ↦ match e with
    | .initial => arithmeticFifthShallowEquiv hπ data H 2 hj u hu
    | .incoming i => fun m b ↦ arithmeticTwoSeedIncoming hπ data H hj u hu m i b
    | .closing => arithmeticFifthShallowClosingEquiv hπ data H 2 hj u hu

local notation "S" => arithmeticTwoSeedState hπ data H hj u hu

/-- The conjugated incoming edge retains its original arithmetic quotient square. -/
theorem arithmeticTwoSeedIncoming_compatible (i : Fin 2) (b : Bool) :
    PolygonArithmeticSimultaneous.CompatibleEquiv
      (fun m ↦ arithmeticTwoSeedIncoming hπ data H hj u hu m i b) := by
  intro m
  unfold arithmeticTwoSeedIncoming
  apply PolygonSmoothing.punctureEquiv_trans_naturality
  · apply PolygonSmoothing.punctureEquiv_trans_naturality
    · exact PolygonSmoothing.punctureEquiv_invert_naturality _
    · fin_cases i
      · exact arithmeticFifthShallowPrecedingEquiv_restriction hπ data H 2 hj u hu m b
      · exact arithmeticFifthShallowIncomingEquiv_restriction hπ data H 2 hj u hu m b
  · exact PolygonSmoothing.punctureEquiv_invert_naturality _

/-- Every seed smoothing and full edge respects the coefficient restrictions. -/
theorem arithmeticTwoSeedState_compatible : (S).Compatible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact arithmeticFifthShallowSmoothing_restriction hπ data H 2 hj u hu
  · intro m i b
    fin_cases i
    · exact arithmeticFifthShallowNeighborSmoothing_restriction hπ data H 2 hj u hu m b
    · exact arithmeticFifthShallowPrecedingSmoothing_restriction hπ data H 2 hj u hu m b
    · exact arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m
  · exact arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 2 hj u hu
  · intro e b
    cases e with
    | initial => exact fun m ↦ arithmeticFifthShallowEquiv_restriction hπ data H 2 hj u hu m b
    | incoming i => exact arithmeticTwoSeedIncoming_compatible hπ data H hj u hu i b
    | closing =>
      exact fun m ↦ arithmeticFifthShallowClosingEquiv_restriction hπ data H 2 hj u hu m b

/-- All actual seed smoothings retain their top-power annihilators. -/
theorem arithmeticTwoSeedState_annihilated : (S).Annihilated := by
  refine ⟨?_, ?_, ?_⟩
  · intro m b
    apply PolygonArithmeticStages.correctionSmoothing_annihilated
    apply PolygonArithmeticStages.correctionSmoothing_annihilated
    exact arithmeticTopSmoothing_annihilated data H m
  · intro m i b
    fin_cases i
    · apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      exact arithmeticFourthEarlierInput_annihilated hπ data H 2 hj u hu m b
    · apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      exact arithmeticFourthPrecedingInput_annihilated hπ data H 2 hj u hu m b
    · exact arithmeticTopSmoothing_annihilated data H m
  · intro m
    apply PolygonArithmeticStages.twoBranchCorrectionRebasedSmoothing_annihilated
    apply PolygonArithmeticStages.twoBranchCorrectionRebasedSmoothing_annihilated
    exact arithmeticFourthTerminalInput_annihilated hπ data H 2 hj u hu m

/-- Every complete seed edge is normalized on the fifth layer, after orientation transport. -/
theorem arithmeticTwoSeedState_normalized : (S).Normalized B 5 := by
  intro e b
  cases e with
  | initial => exact arithmeticFifthShallowEquiv_fifth hπ data H 2 hj u hu b
  | incoming i =>
    change arithmeticTwoSeedIncoming hπ data H hj u hu 5 i b = AlgEquiv.refl
    fin_cases i <;>
      simp only [arithmeticTwoSeedIncoming, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        arithmeticFifthShallowPrecedingEquiv_fifth, arithmeticFifthShallowIncomingEquiv_fifth]
    all_goals
      ext z : 1
      exact LaurentPolynomial.involutive_invert z
  | closing => exact arithmeticFifthShallowClosingEquiv_fifth hπ data H 2 hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
