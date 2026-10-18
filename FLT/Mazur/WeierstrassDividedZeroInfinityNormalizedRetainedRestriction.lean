/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedSeparation

/-!
# Quotient compatibility of the full reparameterized retained edges

The original torus coefficient map commutes with both retained attachments.
The source square follows from the complete comparison, so it keeps the full
Laurent substitution without reducing its coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "N" => closingNormalizedRestriction data H m
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "v" => fun k ↦ arithmeticZeroInfinityNormalizedTargetLeft data H k
local notation "w" => fun k ↦
  arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticZeroInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "q" => arithmeticZeroInfinityNormalizedFullUnionRestriction hπ data H m hj u hu
local notation "t" => arithmeticZeroInfinityNormalizedTargetRestriction data H m

omit [IsDomain R] [IsBezout R] in
/-- The whole left branch has the original coefficient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedLeft_restriction :
    leftBranchOpen (Q m) (τ m) ≫ N = ρ ≫ leftBranchOpen (Q (m + 1)) (τ (m + 1)) :=
  leftBranchOpen_ringMap (restriction R π m).toRingHom _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

omit [IsDomain R] [IsBezout R] in
/-- Each entire retained boundary in the independent pair commutes with quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTargetLeft_restriction (b : Bool) :
    v m b ≫ t = ρ ≫ v (m + 1) b := by
  cases b <;>
    simp only [arithmeticZeroInfinityNormalizedTargetLeft, Bool.false_eq_true, ↓reduceIte,
      Category.assoc, arithmeticZeroInfinityNormalizedTargetRestriction_first,
      arithmeticZeroInfinityNormalizedTargetRestriction_opposite,
      arithmeticZeroInfinityNormalizedLeft_restriction_assoc]

/-- The full reparameterized original attachment retains the original torus quotient map. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedToUnion_restriction (b : Bool) :
    w m b ≫ q = ρ ≫ w (m + 1) b := by
  apply (cancel_mono (F (m + 1)).hom).mp
  simp only [Category.assoc, arithmeticZeroInfinityNormalizedFullComparison_restriction,
    arithmeticZeroInfinityNormalizedRetainedToUnion_comparison,
    arithmeticZeroInfinityNormalizedRetainedToUnion_comparison_assoc,
    arithmeticZeroInfinityNormalizedTargetLeft_restriction]

/-- The full retained-edge domain with its original coefficient maps. -/
def arithmeticZeroInfinityNormalizedEdgeSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ closingOverlapRestriction (R := R) (π := π) k)

/-- Both standard target boundaries assemble at all arithmetic orders. -/
def arithmeticZeroInfinityNormalizedTargetLeftSystem (b : Bool) :
    arithmeticZeroInfinityNormalizedEdgeSystem (R := R) (π := π) ⟶
      arithmeticZeroInfinityNormalizedTargetSystem data H :=
  NatTrans.ofSequence (fun k ↦ v k b) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedEdgeSystem,
      arithmeticZeroInfinityNormalizedTargetSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      (arithmeticZeroInfinityNormalizedTargetLeft_restriction data H k b).symm)

/-- Both reparameterized original source edges assemble at all arithmetic orders. -/
def arithmeticZeroInfinityNormalizedRetainedToUnionSystem (b : Bool) :
    arithmeticZeroInfinityNormalizedEdgeSystem (R := R) (π := π) ⟶
      arithmeticZeroInfinityNormalizedFullUnionSystem hπ data H hj u hu :=
  NatTrans.ofSequence (fun k ↦ w k b) (by
    intro k
    simpa only [arithmeticZeroInfinityNormalizedEdgeSystem,
      arithmeticZeroInfinityNormalizedFullUnionSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      (arithmeticZeroInfinityNormalizedRetainedToUnion_restriction hπ data H k hj u hu b).symm)

/-- The complete pair-system comparison preserves the actual retained-edge system. -/
theorem arithmeticZeroInfinityNormalizedRetainedToUnionSystem_comparison (b : Bool) :
    arithmeticZeroInfinityNormalizedRetainedToUnionSystem hπ data H hj u hu b ≫
      arithmeticZeroInfinityNormalizedFullComparisonSystem hπ data H hj u hu =
        arithmeticZeroInfinityNormalizedTargetLeftSystem data H b := by
  ext k : 2
  exact arithmeticZeroInfinityNormalizedRetainedToUnion_comparison hπ data H k hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
