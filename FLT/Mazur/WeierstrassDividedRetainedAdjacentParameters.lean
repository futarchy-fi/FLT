/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftAtlasEdges
public import FLT.Mazur.WeierstrassRetainedFixedBoundary
public import FLT.Mazur.PolygonSmoothingPunctureGeometry

/-!
# One exact parameter for consecutive normalized retained charts

The outgoing full parameter is an isomorphism. The recurrence identifies it
with the next incoming parameter before either residual correction is applied.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "q" => arithmeticStartOneQuotient W H.a1_unit π m
local notation "hq" => arithmeticStartOneQuotient_relation W H.a1_unit π m
local notation "V" => arithmeticRetainedFullCorrection data H m k hk
local notation "N" => arithmeticRetainedFixedSmoothingIso data H m k hk

/-- The entire outgoing substitution, with inverse supplied by the original closing equivalence. -/
def arithmeticRetainedAdjacentParameter (a : Fin k) : branchTorus Q ≅ branchTorus Q :=
  punctureSpecIso (arithmeticRetainedClosingEquiv data H m k hk a) ≪≫ edgeInversion Q

omit [IsDomain R] in
/-- This is exactly the outgoing full root parameter, including its depth scale. -/
theorem arithmeticRetainedAdjacentParameter_hom (a : Fin k) :
    (arithmeticRetainedAdjacentParameter data H m k hk a).hom =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
        (retainedFixedEdgeUnit t q
          (retainedScaledCorrectionUnit t (retainedDepthScale q 1 a.val) (V a)))).toRingHom) := by
  rw [arithmeticRetainedAdjacentParameter, Iso.trans_hom]
  change Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit
    (arithmeticRetainedClosingUnit data H m k hk a)).toRingHom) ≫ _ = _
  rw [← NodalFiber.unitParameter_inverse]
  simp only [arithmeticRetainedClosingUnit, inv_inv]

omit [IsDomain R] in
/-- The original outgoing branch is transported by that actual invertible parameter. -/
@[reassoc] theorem arithmeticRetainedAdjacentParameter_outgoing (a : Fin k) :
    leftBranchOpen Q t ≫ (N a).hom =
      (arithmeticRetainedAdjacentParameter data H m k hk a).hom ≫ leftBranchOpen Q τ := by
  rw [arithmeticRetainedAdjacentParameter_hom]
  exact retainedFixedSmoothingChart_outgoing ..

include hπ in
/-- The next incoming original branch uses the very same full outgoing parameter. -/
@[reassoc] theorem arithmeticRetainedAdjacentParameter_incoming
    (a : ℕ) (ha : a + 1 < k) :
    precedingBranch Q t ≫ (N ⟨a + 1, ha⟩).hom =
      (arithmeticRetainedAdjacentParameter data H m k hk ⟨a, by omega⟩).hom ≫
        precedingBranch Q τ := by
  rw [arithmeticRetainedAdjacentParameter_hom]
  change precedingBranch Q t ≫ retainedFixedSmoothingChart t τ (q : Q) hq
    (retainedScaledCorrectionUnit t (retainedDepthScale q 1 (a + 1)) (V ⟨a + 1, ha⟩)) = _
  rw [retainedDepthScale_succ]
  exact retainedFixedSmoothingChart_incoming t τ q hq (retainedDepthScale q 1 a)
    (V ⟨a, by omega⟩) (V ⟨a + 1, ha⟩)
    (arithmeticRetainedFullCorrection_adjacent data H m k hk hπ a ha)

end FLT.Mazur.WeierstrassDividedDepth
