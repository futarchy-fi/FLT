/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalBoundaryAlgebra

/-!
# An explicit simultaneous terminal extension from Laurent coefficient equations

The two coordinate candidates are constructed at every arithmetic order.
Their coefficient compatibility, expressed over the actual quotient ring,
constructs the entire node map and both unchanged original closing squares.
This does not assert that the coefficient equations hold at every order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "F" => arithmeticTerminalNormalizationBoundary data H m j hj u hu
local notation "B" => arithmeticRetainedClosingEquiv data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "T" => fixedTerminalPolygonBoundaryParameter data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu

/-- The actual full candidate for either generator, using both original Laurent boundaries. -/
def arithmeticTerminalCoordinateLift (b : Bool) : ChartRing τ :=
  let z := if b then leftCoordinate τ else rightCoordinate τ
  pairedLaurentLift τ (F true z) (LaurentPolynomial.invert (F false z))

/-- Explicit coefficient equations on the two candidates, not an assumed chart map. -/
def ArithmeticTerminalBoundaryCompatible : Prop :=
  LaurentCompatible τ (F true (leftCoordinate τ))
      (LaurentPolynomial.invert (F false (leftCoordinate τ))) ∧
    LaurentCompatible τ (F true (rightCoordinate τ))
      (LaurentPolynomial.invert (F false (rightCoordinate τ)))

variable (h : ArithmeticTerminalBoundaryCompatible data H m j hj u hu)

/-- Compatibility constructs the complete simultaneous correction by polynomial evaluation. -/
def arithmeticTerminalBoundaryExtension : ChartRing τ →ₐ[Q] ChartRing τ :=
  twoBranchLift τ (F true) (F false) h.1 h.2

/-- Its left coordinate is precisely the explicit two-boundary candidate. -/
theorem arithmeticTerminalBoundaryExtension_left :
    arithmeticTerminalBoundaryExtension data H m j hj u hu h (leftCoordinate τ) =
      arithmeticTerminalCoordinateLift data H m j hj u hu true :=
  boundaryLift_left τ τ (F true) (LaurentPolynomial.invert.toAlgHom.comp (F false)) h.1 h.2

/-- Its right coordinate is constructed from the same pair of full original boundaries. -/
theorem arithmeticTerminalBoundaryExtension_right :
    arithmeticTerminalBoundaryExtension data H m j hj u hu h (rightCoordinate τ) =
      arithmeticTerminalCoordinateLift data H m j hj u hu false :=
  boundaryLift_right τ τ (F true) (LaurentPolynomial.invert.toAlgHom.comp (F false)) h.1 h.2

omit h in
/-- The explicit coefficient tests exactly characterize extension of both actual punctures. -/
theorem arithmeticTerminalBoundaryCompatible_iff :
    ArithmeticTerminalBoundaryCompatible data H m j hj u hu ↔
      ∃ N : ChartRing τ →ₐ[Q] ChartRing τ,
        (leftLaurentMap τ).comp N = F true ∧
          ((leftLaurentMap τ).comp (branchSwapMap τ)).comp N = F false := by
  constructor
  · intro hc
    exact ⟨arithmeticTerminalBoundaryExtension data H m j hj u hu hc,
      twoBranchLift_left τ (F true) (F false) hc.1 hc.2,
      twoBranchLift_right τ (F true) (F false) hc.1 hc.2⟩
  · rintro ⟨N, hl, hr⟩
    have hp : (precedingLaurentMap Q τ).comp N =
        LaurentPolynomial.invert.toAlgHom.comp (F false) :=
      congrArg (LaurentPolynomial.invert.toAlgHom.comp) hr
    exact (boundaryLift_exists_iff τ τ (F true)
      (LaurentPolynomial.invert.toAlgHom.comp (F false))).mp ⟨N, hl, hp⟩

/-- Both full puncture equations determine the entire constructed terminal correction. -/
theorem arithmeticTerminalBoundaryExtension_unique (N : ChartRing τ →ₐ[Q] ChartRing τ)
    (hl : (leftLaurentMap τ).comp N = F true)
    (hr : ((leftLaurentMap τ).comp (branchSwapMap τ)).comp N = F false) :
    N = arithmeticTerminalBoundaryExtension data H m j hj u hu h :=
  twoBranchLift_unique τ (F true) (F false) h.1 h.2 N hl hr

/-- The scheme map of the entire original arithmetic terminal node. -/
def arithmeticTerminalBoundaryExtensionMap :
    PolygonSmoothing.chart Q τ ⟶ PolygonSmoothing.chart Q τ :=
  twoBranchLiftMap τ (F true) (F false) h.1 h.2

/-- Both punctures of the single constructed node map recover the prescribed algebra maps. -/
@[reassoc] theorem arithmeticTerminalBoundaryExtensionMap_branch (b : Bool) :
    (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) ≫
      arithmeticTerminalBoundaryExtensionMap data H m j hj u hu h =
        Spec.map (CommRingCat.ofHom (F b).toRingHom) := by
  cases b
  · exact twoBranchLiftMap_right τ (F true) (F false) h.1 h.2
  · exact twoBranchLiftMap_left τ (F true) (F false) h.1 h.2

/-- Both original source overlaps now reach the unchanged retained closing parameter. -/
@[reassoc] theorem arithmeticTerminalBoundaryExtensionMap_corrected (b : Bool) :
    T b ≫ (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) ≫
      arithmeticTerminalBoundaryExtensionMap data H m j hj u hu h =
        Spec.map (CommRingCat.ofHom (B).toAlgHom.toRingHom) ≫
          (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) := by
  rw [arithmeticTerminalBoundaryExtensionMap_branch,
    arithmeticTerminalNormalizationBoundary_square]

/-- The full terminal correction preserves the actual arithmetic coefficient map. -/
@[reassoc] theorem arithmeticTerminalBoundaryExtensionMap_base :
    arithmeticTerminalBoundaryExtensionMap data H m j hj u hu h ≫ chartStructure Q τ =
      chartStructure Q τ :=
  twoBranchLiftMap_base τ (F true) (F false) h.1 h.2

end FLT.Mazur.WeierstrassDividedDepth
