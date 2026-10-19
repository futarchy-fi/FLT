/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSourceDesc
public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceEdges

/-!
# The universal descent map for the five actual cyclic source nodes

Only the five exact seed-edge equations are required. The construction uses
the original full source pushouts and retains both reflected entire nodes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] arithmeticZeroDiagonalAtlasChart
  finiteGlobalModel finiteGlobalContraction arithmeticZeroFiniteAtlasIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "A" => arithmeticZeroDiagonalAtlasObject hπ data H m hj u hu
variable {Y : Scheme}
variable (f : ∀ i, PolygonSmoothing.chart (Quotient R π m) (((arithmeticZeroCyclicSeed hπ data H hj
    u hu)).parameter m i) ⟶ Y)
variable (hf : ∀ i, leftBranchOpen (Quotient R π m) (((arithmeticZeroCyclicSeed hπ data H hj u
    hu)).parameter m i) ≫ f i =
    (punctureSpecIso (((arithmeticZeroCyclicSeed hπ data H hj u hu)).edge m i)).hom ≫
      rightBranchOpen (Quotient R π m) (((arithmeticZeroCyclicSeed hπ data H hj u hu)).parameter m
    (zeroCyclicSuccessor i)) ≫ f (zeroCyclicSuccessor i))

/-- Unreflect the two specified whole initial maps for the original full pair pushout. -/
def arithmeticZeroCyclicDescInitial (b : Bool) : PolygonSmoothing.chart Q τ ⟶ Y :=
  match b with
  | false => f (.initial false)
  | true => (branchSwapIso Q τ).hom ≫ f (.initial true)

/-- Unreflect both retained maps without changing any original smoothing. -/
def arithmeticZeroCyclicDescRetained (b : Bool) : A (.retained ⟨0, by omega⟩ b) ⟶ Y :=
  match b with
  | false => f (.retained false)
  | true => (branchSwapIso Q ((D).last m true)).hom ≫ f (.retained true)

local notation "a" => arithmeticZeroCyclicDescInitial hπ data H m hj u hu f
local notation "s" => arithmeticZeroCyclicDescRetained hπ data H m hj u hu f

omit [IsBezout R] in
include hf in
/-- The oriented common edge is exactly the whole initial-pair pushout equation. -/
theorem arithmeticZeroCyclicDescInitial_common :
    rightBranchOpen Q τ ≫ a false = (edgeInversion Q).hom ≫ rightBranchOpen Q τ ≫ a true := by
  change rightBranchOpen Q τ ≫ f (.initial false) =
    (edgeInversion Q).hom ≫ rightBranchOpen Q τ ≫
      (branchSwapIso Q τ).hom ≫ f (.initial true)
  rw [rightBranchOpen_branchSwapIso_assoc]
  erw [hf (.initial true)]
  erw [← Category.assoc,
    LaurentUnitPoints.edgeInversion_comp_self, Category.id_comp]
  rfl

omit [IsBezout R] in
include hf in
/-- Both exact original retained attachments follow from the corresponding oriented edges. -/
theorem arithmeticZeroCyclicDescInitial_retained (b : Bool) :
    leftBranchOpen Q τ ≫ a b =
      arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu b ≫ s b := by
  rw [← arithmeticZeroRetainedEdgeEquiv_side hπ data H m hj u hu b, Category.assoc]
  cases b
  · exact hf (.initial false)
  · change leftBranchOpen Q τ ≫ (branchSwapIso Q τ).hom ≫ f (.initial true) =
      (punctureSpecIso (arithmeticZeroRetainedEdgeEquiv hπ data H m hj u hu true)).hom ≫
        rightBranchOpen Q ((D).last m true) ≫
          (branchSwapIso Q ((D).last m true)).hom ≫ f (.retained true)
    rw [leftBranchOpen_branchSwapIso_assoc, rightBranchOpen_branchSwapIso_assoc]
    erw [hf (.retained true)]
    simp only [arithmeticZeroCyclicSeed, punctureSpecIso_symm, Iso.symm_hom,
      Iso.hom_inv_id_assoc]
    rfl

omit [IsBezout R] in
include hf in
/-- Both original closing equations retain their one common complete terminal map. -/
theorem arithmeticZeroCyclicDescRetained_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).last m b) ≫ s b =
      punctureOpen ((D).terminal m) b ≫ f .terminal := by
  cases b
  · change (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).last m false) ≫
      f (.retained false) = punctureOpen ((D).terminal m) false ≫ f .terminal
    erw [hf (.retained false)]
    rw [punctureOpen_false]
    change (edgeInversion Q).hom ≫ (edgeInversion Q).hom ≫ _ = _
    rw [← Category.assoc, LaurentUnitPoints.edgeInversion_comp_self, Category.id_comp]
    rfl
  · change (edgeInversion Q).hom ≫ leftBranchOpen Q ((D).last m true) ≫
      (branchSwapIso Q ((D).last m true)).hom ≫ f (.retained true) =
        punctureOpen ((D).terminal m) true ≫ f .terminal
    rw [leftBranchOpen_branchSwapIso_assoc, punctureOpen_true]
    exact (hf .terminal).symm

/-- The five exact compatible whole-node maps descend to the actual original source. -/
def arithmeticZeroCyclicSourceDesc :
    simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu ⟶ Y :=
  arithmeticZeroSourceDesc hπ data H m hj u hu a
    (by simpa only [Category.assoc] using
      arithmeticZeroCyclicDescInitial_common hπ data H m hj u hu f hf) s
    (arithmeticZeroCyclicDescInitial_retained hπ data H m hj u hu f hf) (f .terminal)
    (arithmeticZeroCyclicDescRetained_closing hπ data H m hj u hu f hf)

/-- Descent recovers every entire cyclic source node, including both coordinate swaps. -/
@[reassoc] theorem arithmeticZeroCyclicSourceDesc_chart (i : ZeroCyclicVertex) :
    arithmeticZeroCyclicSourceChart hπ data H m hj u hu i ≫
      arithmeticZeroCyclicSourceDesc hπ data H m hj u hu f hf = f i := by
  rcases i with _ | (_ | _) | (_ | _) <;>
    simp only [arithmeticZeroCyclicSourceChart, arithmeticZeroCyclicSourceDesc, Category.assoc,
      arithmeticZeroSourceDesc_terminal, arithmeticZeroSourceDesc_retained,
      arithmeticZeroSourceDesc_initial, arithmeticZeroCyclicDescInitial,
      arithmeticZeroCyclicDescRetained] <;>
    simp only [← Category.assoc, branchSwapIso_involutive] <;> exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
