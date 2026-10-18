/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthTerminalTransport
public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasOverlaps

/-!
# Original terminal punctures in the full diagonal atlas

All accumulated terminal corrections carry the original full puncture by an
isomorphism. The finite rounds retain their actual changed smoothings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
local notation "Q" => Quotient R π m
local notation "r" => arithmeticOriginalClosingBoundary data H m 0 hj

/-- The first depth-zero correction leaves the common fourth terminal intact. -/
theorem arithmeticZeroFirstAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticZeroFirstAtlasIso hπ data H m hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticFourthTerminalSmoothing hπ data H 0 hj u hu m) b := by
  simpa only [arithmeticZeroFirstAtlasIso, arithmeticZeroFirstAtlasCorrection,
    Iso.trans_refl] using
    arithmeticFourthOuterAtlasIso_terminal_transport hπ data H m 0 hj u hu b

/-- The second depth-zero terminal retains the complete original boundary. -/
theorem arithmeticZeroSecondAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticZeroSecondAtlasIso hπ data H m hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticZeroSecondTerminalSmoothing hπ data H 0 hj u hu m) b := by
  obtain ⟨e, he⟩ := arithmeticZeroFirstAtlasIso_terminal_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
    (arithmeticFourthTerminalSmoothing hπ data H 0 hj u hu m)
    (arithmeticZeroSecondTerminalIntegralField hπ data H 0 hj u hu) b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticZeroSecondTerminalIso_puncture hπ data H m 0 hj u hu b)

/-- The third depth-zero terminal retains the complete original boundary. -/
theorem arithmeticZeroThirdAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticZeroThirdAtlasIso hπ data H m hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticZeroThirdTerminalSmoothing hπ data H 0 hj u hu m) b := by
  obtain ⟨e, he⟩ := arithmeticZeroSecondAtlasIso_terminal_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
    (arithmeticZeroSecondTerminalSmoothing hπ data H 0 hj u hu m)
    (arithmeticZeroThirdTerminalIntegralField hπ data H 0 hj u hu) b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticZeroThirdTerminalIso_puncture hπ data H m 0 hj u hu b)

/-- The fourth depth-zero terminal retains the complete original boundary. -/
theorem arithmeticZeroFourthAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticZeroFourthAtlasIso hπ data H m hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticZeroFourthTerminalSmoothing hπ data H 0 hj u hu m) b := by
  obtain ⟨e, he⟩ := arithmeticZeroThirdAtlasIso_terminal_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
    (arithmeticZeroThirdTerminalSmoothing hπ data H 0 hj u hu m)
    (arithmeticZeroFourthTerminalIntegralField hπ data H 0 hj u hu) b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticZeroFourthTerminalIso_puncture hπ data H m 0 hj u hu b)

/-- The fifth depth-zero terminal retains the complete original boundary. -/
theorem arithmeticZeroFifthAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticZeroFifthAtlasIso hπ data H m hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticZeroFifthTerminalSmoothing hπ data H 0 hj u hu m) b := by
  obtain ⟨e, he⟩ := arithmeticZeroFourthAtlasIso_terminal_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
    (arithmeticZeroFourthTerminalSmoothing hπ data H 0 hj u hu m)
    (arithmeticZeroFifthTerminalIntegralField hπ data H 0 hj u hu) b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticZeroFifthTerminalIso_puncture hπ data H m 0 hj u hu b)

/-- Every finite correction transports both full original terminal punctures. -/
theorem arithmeticZeroFiniteAtlasIso_terminal_transport (k : ℕ) (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticZeroFiniteAtlasIso hπ data H k m hj u hu .terminal).hom =
        e.hom ≫ punctureOpen
          ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).terminal m) b := by
  obtain ⟨e, he⟩ := arithmeticZeroFifthAtlasIso_terminal_transport hπ data H m hj u hu b
  refine ⟨e ≪≫ punctureSpecIso
    (arithmeticZeroFiniteTerminalPunctureEquiv hπ data H 0 hj u hu k m b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticZeroFiniteTerminalIso_puncture hπ data H k m 0 hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
