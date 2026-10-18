/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainIteration
public import FLT.Mazur.WeierstrassDividedFifthFartherIncomingRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowJointRestriction
public import FLT.Mazur.WeierstrassDividedFifthShallowResidualRestriction
public import FLT.Mazur.WeierstrassDividedFifthDeepEndCancellation

/-!
# The actual depth-three seed in uniform retained-chain coordinates

Conjugate all three internal edges by inversion at both endpoints. The last
node keeps its original smoothing. Scheme chart identifications are separate.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFifthDeepIncomingEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 3 hj

local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The actual internal edge in inverse-left to right coordinates. -/
def arithmeticThreeSeedIncoming (m : ℕ) (i : Fin 3) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (LaurentPolynomial.invert.trans
    (if i = 0 then arithmeticFifthFartherIncomingEquiv hπ data H 3 hj u hu m b
      else if i = 1 then arithmeticFifthDeepPrecedingEquiv hπ data H 3 hj u hu m b
      else arithmeticFifthDeepIncomingEquiv hπ data H 3 hj u hu m b)).trans
        LaurentPolynomial.invert

/-- The fifth depth-three packet supplies four retained nodes and the two boundary edges. -/
def arithmeticThreeSeedState : State R π 3 where
  initial := arithmeticFifthFartherSmoothing hπ data H 3 hj u hu
  retained := fun m i b ↦ if i = 0 then
    arithmeticFifthFartherNeighborSmoothing hπ data H 3 hj u hu m b else if i = 1 then
      arithmeticFifthDeepSmoothing hπ data H 3 hj u hu .outer m b else if i = 2 then
        arithmeticFifthDeepSmoothing hπ data H 3 hj u hu .predecessor m b else τ m
  terminal := arithmeticFifthShallowTerminalSmoothing hπ data H 3 hj u hu
  edgeEquiv := fun e ↦ match e with
    | .initial => arithmeticFifthFartherEquiv hπ data H 3 hj u hu
    | .incoming i => fun m b ↦ arithmeticThreeSeedIncoming hπ data H hj u hu m i b
    | .closing => arithmeticFifthShallowClosingEquiv hπ data H 3 hj u hu

local notation "S" => arithmeticThreeSeedState hπ data H hj u hu

/-- The conjugated incoming edge retains its original arithmetic quotient square. -/
theorem arithmeticThreeSeedIncoming_compatible (i : Fin 3) (b : Bool) :
    PolygonArithmeticSimultaneous.CompatibleEquiv
      (fun m ↦ arithmeticThreeSeedIncoming hπ data H hj u hu m i b) := by
  intro m
  unfold arithmeticThreeSeedIncoming
  apply PolygonSmoothing.punctureEquiv_trans_naturality
  · apply PolygonSmoothing.punctureEquiv_trans_naturality
    · exact PolygonSmoothing.punctureEquiv_invert_naturality _
    · fin_cases i
      · exact arithmeticFifthFartherIncomingEquiv_restriction hπ data H 3 hj u hu m b
      · exact arithmeticFifthDeepPrecedingEquiv_restriction hπ data H 3 hj u hu m b
      · exact arithmeticFifthDeepIncomingEquiv_restriction hπ data H 3 hj u hu m b
  · exact PolygonSmoothing.punctureEquiv_invert_naturality _

/-- Every seed smoothing and full edge respects the coefficient restrictions. -/
theorem arithmeticThreeSeedState_compatible : (S).Compatible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact arithmeticFifthFartherSmoothing_restriction hπ data H 3 hj u hu
  · intro m i b
    fin_cases i
    · exact arithmeticFifthFartherNeighborSmoothing_restriction hπ data H 3 hj u hu m b
    · exact arithmeticFifthDeepSmoothing_restriction hπ data H 3 hj u hu m .outer b
    · exact arithmeticFifthDeepSmoothing_restriction hπ data H 3 hj u hu m .predecessor b
    · exact arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m
  · exact arithmeticFifthShallowTerminalSmoothing_restriction hπ data H 3 hj u hu
  · intro e b
    cases e with
    | initial => exact fun m ↦ arithmeticFifthFartherEquiv_restriction hπ data H 3 hj u hu m b
    | incoming i => exact arithmeticThreeSeedIncoming_compatible hπ data H hj u hu i b
    | closing =>
      exact fun m ↦ arithmeticFifthShallowClosingEquiv_restriction hπ data H 3 hj u hu m b

/-- All actual seed smoothings retain their top-power annihilators. -/
theorem arithmeticThreeSeedState_annihilated : (S).Annihilated := by
  refine ⟨?_, ?_, ?_⟩
  · intro m b
    apply PolygonArithmeticStages.correctionSmoothing_annihilated
    exact arithmeticTopSmoothing_annihilated data H m
  · intro m i b
    fin_cases i
    · apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      apply PolygonArithmeticStages.correctionSmoothing_annihilated
      exact arithmeticTopSmoothing_annihilated data H m
    · apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      exact arithmeticFifthDeepInput_annihilated hπ data H 3 hj u hu .outer m b
    · apply PolygonArithmeticStages.twoBranchCorrectionSmoothing_annihilated
      exact arithmeticFifthDeepInput_annihilated hπ data H 3 hj u hu .predecessor m b
    · exact arithmeticTopSmoothing_annihilated data H m
  · intro m
    apply PolygonArithmeticStages.twoBranchCorrectionRebasedSmoothing_annihilated
    apply PolygonArithmeticStages.twoBranchCorrectionRebasedSmoothing_annihilated
    exact arithmeticFourthTerminalInput_annihilated hπ data H 3 hj u hu m

/-- Every complete seed edge is normalized on the fifth layer, after orientation transport. -/
theorem arithmeticThreeSeedState_normalized : (S).Normalized B 5 := by
  intro e b
  cases e with
  | initial => exact arithmeticFifthFartherEquiv_fifth hπ data H 3 hj u hu b
  | incoming i =>
    change arithmeticThreeSeedIncoming hπ data H hj u hu 5 i b = AlgEquiv.refl
    fin_cases i <;>
      simp only [arithmeticThreeSeedIncoming, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        arithmeticFifthFartherIncomingEquiv_fifth, arithmeticFifthDeepPrecedingEquiv_fifth,
        arithmeticFifthDeepIncomingEquiv_fifth]
    all_goals
      ext z : 1
      exact LaurentPolynomial.involutive_invert z
  | closing => exact arithmeticFifthShallowClosingEquiv_fifth hπ data H 3 hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
