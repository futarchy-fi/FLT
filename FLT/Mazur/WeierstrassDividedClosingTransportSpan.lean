/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalEdgeCorrection
public import FLT.Mazur.WeierstrassDividedRetainedChartIso
public import FLT.Mazur.WeierstrassRetainedFixedBoundary
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# Transport the original closing span through full chart isomorphisms

The target attachment is twisted by the exact terminal and retained
parameters. The original source arrows are unchanged. Both Boolean terminal
branches have a constructed comparison on whole nodes and their full overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "v" => arithmeticRetainedClosingUnit data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))
local notation "T" => fixedTerminalPolygonBoundaryParameter data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "E" => terminalArithmeticNodeEvaluation data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "P" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu m

local notation "C" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))

/-- The normalized retained puncture uses the reciprocal closing coordinate. -/
def arithmeticClosingRetainedBoundary : branchTorus Q ⟶ PolygonSmoothing.chart Q τ :=
  (edgeInversion Q).hom ≫ leftBranchOpen Q τ

/-- The target transition is transported from both full original parameter maps. -/
def arithmeticClosingTerminalTwist (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (asIso B).symm ≪≫ asIso (T b)

/-- The terminal target arrow retains the whole transported transition. -/
def arithmeticClosingTerminalBoundary (b : Bool) :
    branchTorus Q ⟶ PolygonSmoothing.chart Q τ :=
  (arithmeticClosingTerminalTwist data H m j hj u hu b).hom ≫
    (if b then leftBranchOpen Q τ else rightBranchOpen Q τ)

instance arithmeticClosingRetainedBoundary_isOpenImmersion :
    IsOpenImmersion (arithmeticClosingRetainedBoundary data H m) := by
  unfold arithmeticClosingRetainedBoundary
  infer_instance

instance arithmeticClosingTerminalBoundary_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticClosingTerminalBoundary data H m j hj u hu b) := by
  unfold arithmeticClosingTerminalBoundary
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The original retained edge agrees with its transported full target puncture. -/
@[reassoc] theorem arithmeticClosingSpan_retained :
    leftBranchOpen Q (parameter R π m) ≫ (C).hom =
      B ≫ arithmeticClosingRetainedBoundary data H m := by
  change leftBranchOpen Q (parameter R π m) ≫
    retainedFixedSmoothingChart _ _ _ _ _ = _
  rw [retainedFixedSmoothingChart_outgoing, arithmeticClosingRetainedBoundary,
    ← Category.assoc, ← NodalFiber.unitParameter_inverse]
  simp only [arithmeticRetainedClosingUnit, inv_inv]

/-- The source terminal arrow is kept intact when transporting the closing span. -/
@[reassoc] theorem arithmeticClosingSpan_terminal (b : Bool) :
    Spec.map (CommRingCat.ofHom (E b).toRingHom) ≫ (P).hom =
      B ≫ arithmeticClosingTerminalBoundary data H m j hj u hu b := by
  rw [fixedTerminalPolygon_boundary, arithmeticClosingTerminalBoundary,
    arithmeticClosingTerminalTwist, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    ← Category.assoc B, ← Category.assoc B, IsIso.hom_inv_id, Category.id_comp]

/-- Both whole charts and the full original overlap form an isomorphic span. -/
def arithmeticClosingSpanIso (b : Bool) :
    span (leftBranchOpen Q (parameter R π m))
        (Spec.map (CommRingCat.ofHom (E b).toRingHom)) ≅
      span (arithmeticClosingRetainedBoundary data H m)
        (arithmeticClosingTerminalBoundary data H m j hj u hu b) :=
  spanIsoMk (asIso B) C P (arithmeticClosingSpan_retained data H m j hj)
    (arithmeticClosingSpan_terminal data H m j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
