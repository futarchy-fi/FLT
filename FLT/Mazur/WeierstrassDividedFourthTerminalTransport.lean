/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterAtlas
public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry
public import FLT.Mazur.PullbackOneLegTransport

/-!
# Full terminal boundary transport through the first four correction rounds

The original Laurent boundary is carried by a complete Laurent isomorphism
at each round. Its coefficients are retained, rather than replaced by inversion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "r" => arithmeticOriginalClosingBoundary data H m j hj
local notation "T" => fixedTerminalPolygonBoundaryParameter data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu

omit [IsBezout R] in
/-- The first whole terminal rescaling retains the full original boundary parameter. -/
theorem changedArithmeticAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (changedArithmeticAtlasIso hπ data H m j hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticTerminalChangedSmoothing data H m j hj u hu) b := by
  refine ⟨asIso (T b) ≪≫ edgeScalingIso
    (arithmeticTerminalTangentScale data H m j hj u hu b), ?_⟩
  simp only [changedArithmeticAtlasIso, twistedArithmeticAtlasIso,
    changedArithmeticAtlasToTwisted, Iso.symm_symm_eq, Iso.trans_hom, Category.assoc,
    arithmeticOriginalClosingBoundary, fixedTerminalPolygon_boundary_assoc,
    arithmeticTerminalChangedIso_branch, asIso_hom]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, punctureOpen_false,
    punctureOpen_true]

omit [IsBezout R] in
/-- The lifted terminal correction transports the entire original puncture. -/
theorem arithmeticResidualLiftAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticResidualLiftAtlasIso hπ data H m j hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu) b := by
  obtain ⟨e, he⟩ := changedArithmeticAtlasIso_terminal_transport hπ data H m j hj u hu b
  refine ⟨e ≪≫ punctureSpecIso
    (arithmeticResidualLiftTerminalPuncture hπ data H m j hj u hu b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticResidualLiftTerminalIso_puncture hπ data H m j hj u hu b)

omit [IsBezout R] in
/-- The second common terminal still carries the complete original Laurent boundary. -/
theorem arithmeticSecondJointAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticSecondJointAtlasIso hπ data H m j hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m) b := by
  obtain ⟨e, he⟩ := arithmeticResidualLiftAtlasIso_terminal_transport hπ data H m j hj u hu b
  refine ⟨e ≪≫ punctureSpecIso
    (arithmeticSecondResidualLiftTerminalPuncture hπ data H m j hj u hu b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticSecondResidualLiftTerminalIso_puncture hπ data H m j hj u hu b)

omit [IsBezout R] in
/-- The third correction retains both full terminal boundary transports. -/
theorem arithmeticThirdAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticThirdAtlasIso hπ data H m j hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m) b := by
  obtain ⟨e, he⟩ := arithmeticSecondJointAtlasIso_terminal_transport hπ data H m j hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
    (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m)
    (arithmeticThirdTerminalIntegralField hπ data H j hj u hu) b).symm, ?_⟩
  exact PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
    (arithmeticThirdTerminalIso_puncture hπ data H j hj u hu m b)

omit [IsBezout R] in
/-- The fourth outer atlas retains the original terminal overlap as a full puncture. -/
theorem arithmeticFourthOuterAtlasIso_terminal_transport (b : Bool) :
    ∃ e : branchTorus Q ≅ branchTorus Q,
      r b ≫ (arithmeticFourthOuterAtlasIso hπ data H m j hj u hu .terminal).hom =
        e.hom ≫ punctureOpen (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) b := by
  obtain ⟨e, he⟩ := arithmeticThirdAtlasIso_terminal_transport hπ data H m j hj u hu b
  refine ⟨e ≪≫ punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
    (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m)
    (arithmeticFourthTerminalIntegralField hπ data H j hj u hu) b).symm, ?_⟩
  simpa only [arithmeticFourthOuterAtlasIso, arithmeticFourthOuterAtlasCorrection,
    arithmeticFourthInitialAtlasCorrection, arithmeticFourthAtlasCorrection,
    arithmeticThirdInitialAtlasIso,
    arithmeticThirdInitialAtlasCorrection, Iso.trans_refl] using
    PullbackOneLegTransport.arrow_trans _ _ _ _ _ e _ he
      (arithmeticFourthTerminalIso_puncture hπ data H j hj u hu m b)

end FLT.Mazur.WeierstrassDividedDepth
