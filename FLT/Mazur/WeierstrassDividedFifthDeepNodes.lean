/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthPairedNodes
public import FLT.Mazur.WeierstrassDividedFourthOuterRestriction
public import FLT.Mazur.WeierstrassDividedFourthSmoothingAnnihilation
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# The three full fifth node factors along the outer retained chain

The predecessor, outer node and farther node start at their actual fourth
smoothings. Every shared edge chooses the same complete residual at both ends.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
/-- The retained positions already modified by the fourth outer atlas. -/
inductive FifthDeepNode
  | predecessor
  | outer
  | farther

/-- The complete outgoing error at each position. -/
def fifthDeepOutgoing : FifthDeepNode → FourthResidualEdge
  | .predecessor => .incoming
  | .outer => .outerPreceding
  | .farther => .outerIncoming

/-- The complete incoming error at each position, including the farther compensation. -/
def fifthDeepIncoming : FifthDeepNode → FourthResidualEdge
  | .predecessor => .outerPreceding
  | .outer => .outerIncoming
  | .farther => .fartherIncoming

variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
/-- The full fourth input at each selected retained position. -/
def arithmeticFifthDeepInput (v : FifthDeepNode) (m : ℕ) (b : Bool) : Quotient R π m :=
  match v with
  | .predecessor => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b
  | .outer => arithmeticFourthOuterSmoothing hπ data H j hj u hu m b
  | .farther => arithmeticFourthFartherSmoothing hπ data H j hj u hu m b

local notation "s" => arithmeticFifthDeepInput hπ data H j hj u hu
local notation "P" => fun v ↦ arithmeticFifthPairedIntegralField hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v)

/-- Every actual fourth input retains the top-power annihilator at every order. -/
theorem arithmeticFifthDeepInput_annihilated (v : FifthDeepNode) (m : ℕ) (b : Bool) :
    parameter R π m ^ m * s v m b = 0 := by
  cases v
  · apply twoBranchCorrectionSmoothing_annihilated
    exact arithmeticFourthPrecedingInput_annihilated hπ data H j hj u hu m b
  · apply twoBranchCorrectionSmoothing_annihilated
    exact arithmeticFourthEarlierInput_annihilated hπ data H j hj u hu m b
  · apply correctionSmoothing_annihilated
    exact arithmeticTopSmoothing_annihilated data H m

/-- The actual previous smoothings retain their original coefficient restrictions. -/
theorem arithmeticFifthDeepInput_restriction (v : FifthDeepNode) (m : ℕ) (b : Bool) :
    restriction R π m (s v (m + 1) b) = s v m b := by
  cases v
  · exact arithmeticFourthPrecedingSmoothing_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthOuterSmoothing_restriction hπ data H j hj u hu m b
  · exact arithmeticFourthFartherSmoothing_restriction hπ data H j hj u hu m b

/-- Each full fifth smoothing retains all earlier scalar drifts. -/
def arithmeticFifthDeepSmoothing (v : FifthDeepNode) (m : ℕ) (b : Bool) : Quotient R π m :=
  arithmeticFifthPairedSmoothing hπ data H j hj u hu
    (fifthDeepOutgoing v) (fifthDeepIncoming v) m (s v m b) b

/-- Both incident fields extend over the same full node with its actual fourth input. -/
def arithmeticFifthDeepFactor (v : FifthDeepNode) (m : ℕ) (b : Bool) :
    ChartRing (arithmeticFifthDeepSmoothing hπ data H j hj u hu v m b) ≃ₐ[Quotient R π m]
      ChartRing (s v m b) :=
  arithmeticFifthPairedFactor hπ data H j hj u hu
    (fifthDeepOutgoing v) (fifthDeepIncoming v) m (s v m b) b

/-- Both punctures are induced by the same entire fifth factor. -/
theorem arithmeticFifthDeepFactor_puncture (v : FifthDeepNode) (m : ℕ) (b a : Bool) :
    (punctureLaurentMap (s v m b) a).comp
        (arithmeticFifthDeepFactor hπ data H j hj u hu v m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s v m b) (P v b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFifthDeepSmoothing hπ data H j hj u hu v m b) a) :=
  arithmeticFifthPairedFactor_puncture hπ data H j hj u hu
    (fifthDeepOutgoing v) (fifthDeepIncoming v) m (s v m b) b a

/-- The complete old smoothing is preserved at layer five at all three positions. -/
theorem arithmeticFifthDeepSmoothing_fifth (v : FifthDeepNode) (b : Bool) :
    arithmeticFifthDeepSmoothing hπ data H j hj u hu v 5 b = s v 5 b :=
  arithmeticFifthPairedSmoothing_fifth hπ data H j hj u hu
    (fifthDeepOutgoing v) (fifthDeepIncoming v) (s v 5 b)
    (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu v 5 b) b

/-- Both full punctures realize the chosen residual projections on the fifth layer. -/
theorem arithmeticFifthDeepPuncture_fifth (v : FifthDeepNode) (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5 (s v 5 b) (P v b) a =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 5 ^ 5)
        (nextCorrectionParameter_square R π 4) (correctionField R π 5
          (arithmeticFifthPairedField hπ data H j hj u hu
            (fifthDeepOutgoing v) (fifthDeepIncoming v) b a)) :=
  arithmeticFifthPairedPuncture_fifth hπ data H j hj u hu
    (fifthDeepOutgoing v) (fifthDeepIncoming v) (s v 5 b)
    (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu v 5 b) b a

end FLT.Mazur.WeierstrassDividedDepth
