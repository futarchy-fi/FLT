/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedExteriorEdges
public import FLT.Mazur.WeierstrassDividedRetainedAdjacentParameters

/-!
# Original full retained nodes in the revised polygon

The original normalization and its full parameter recurrence are retained at
all depths. Consecutive maps agree before the first-order closing correction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "N" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
local notation "O" => twistedRetainedOrientation data H m
local notation "c" => arithmeticRevisedPolygonRetainedChart data H m j hj u hu

/-- Every original retained chart maps using its full normalization and original orientation. -/
def arithmeticOriginalRevisedRetainedMap (a : Fin (j + 1)) (b : Bool) :
    PolygonSmoothing.chart Q t ⟶ arithmeticRevisedPolygon data H m j hj u hu :=
  (N a).hom ≫ (O b).hom ≫ c a b

instance arithmeticOriginalRevisedRetainedMap_isOpenImmersion (a : Fin (j + 1)) (b : Bool) :
    IsOpenImmersion (arithmeticOriginalRevisedRetainedMap data H m j hj u hu a b) := by
  unfold arithmeticOriginalRevisedRetainedMap
  infer_instance

variable [IsDomain R] (hπ : π ≠ 0)
include hπ

/-- The full original consecutive arrows agree in the independent revised target. -/
@[reassoc] theorem arithmeticOriginalRevisedRetainedMap_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    leftBranchOpen Q t ≫
        arithmeticOriginalRevisedRetainedMap data H m j hj u hu ⟨a, by omega⟩ b =
      precedingBranch Q t ≫
        arithmeticOriginalRevisedRetainedMap data H m j hj u hu ⟨a + 1, ha⟩ b := by
  simp only [arithmeticOriginalRevisedRetainedMap]
  rw [← Category.assoc (leftBranchOpen Q t), arithmeticRetainedAdjacentParameter_outgoing,
    ← Category.assoc (precedingBranch Q t),
    arithmeticRetainedAdjacentParameter_incoming hπ, Category.assoc, Category.assoc,
    arithmeticRevisedPolygon_adjacent]

end FLT.Mazur.WeierstrassDividedDepth
