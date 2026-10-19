/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedSeparation

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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "N" => closingNormalizedRestriction data H m
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "v" => fun k ↦ arithmeticOneInfinityNormalizedTargetLeft data H k
local notation "w" => fun k ↦
  arithmeticOneInfinityNormalizedRetainedToUnion hπ data H k hj u hu
local notation "F" => fun k ↦ arithmeticOneInfinityNormalizedFullComparison hπ data H k hj u hu
local notation "q" => arithmeticOneInfinityNormalizedFullUnionRestriction hπ data H m hj u hu
local notation "t" => arithmeticOneInfinityNormalizedTargetRestriction data H m

omit [IsDomain R] [IsBezout R] in
/-- The whole left branch has the original coefficient square. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedLeft_restriction :
    leftBranchOpen (Q m) (τ m) ≫ N = ρ ≫ leftBranchOpen (Q (m + 1)) (τ (m + 1)) :=
  leftBranchOpen_ringMap (restriction R π m).toRingHom _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)

omit [IsDomain R] [IsBezout R] in
/-- Each entire retained boundary in the independent pair commutes with quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedTargetLeft_restriction (b : Bool) :
    v m b ≫ t = ρ ≫ v (m + 1) b := by
  cases b <;>
    simp only [arithmeticOneInfinityNormalizedTargetLeft, Bool.false_eq_true, ↓reduceIte,
      Category.assoc, arithmeticOneInfinityNormalizedTargetRestriction_first,
      arithmeticOneInfinityNormalizedTargetRestriction_opposite,
      arithmeticOneInfinityNormalizedLeft_restriction_assoc]

/-- The full reparameterized original attachment retains the original torus quotient map. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedToUnion_restriction (b : Bool) :
    w m b ≫ q = ρ ≫ w (m + 1) b := by
  apply (cancel_mono (F (m + 1)).hom).mp
  simp only [Category.assoc, arithmeticOneInfinityNormalizedFullComparison_restriction,
    arithmeticOneInfinityNormalizedRetainedToUnion_comparison,
    arithmeticOneInfinityNormalizedRetainedToUnion_comparison_assoc,
    arithmeticOneInfinityNormalizedTargetLeft_restriction]

/-- The full retained-edge domain with its original coefficient maps. -/
def arithmeticOneInfinityNormalizedEdgeSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦ closingOverlapRestriction (R := R) (π := π) k)

/-- Both standard target boundaries assemble at all arithmetic orders. -/
def arithmeticOneInfinityNormalizedTargetLeftSystem (b : Bool) :
    arithmeticOneInfinityNormalizedEdgeSystem (R := R) (π := π) ⟶
      arithmeticOneInfinityNormalizedTargetSystem data H :=
  NatTrans.ofSequence (fun k ↦ v k b) (by
    intro k
    simpa only [arithmeticOneInfinityNormalizedEdgeSystem,
      arithmeticOneInfinityNormalizedTargetSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      (arithmeticOneInfinityNormalizedTargetLeft_restriction data H k b).symm)

/-- Both reparameterized original source edges assemble at all arithmetic orders. -/
def arithmeticOneInfinityNormalizedRetainedToUnionSystem (b : Bool) :
    arithmeticOneInfinityNormalizedEdgeSystem (R := R) (π := π) ⟶
      arithmeticOneInfinityNormalizedFullUnionSystem hπ data H hj u hu :=
  NatTrans.ofSequence (fun k ↦ w k b) (by
    intro k
    simpa only [arithmeticOneInfinityNormalizedEdgeSystem,
      arithmeticOneInfinityNormalizedFullUnionSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      (arithmeticOneInfinityNormalizedRetainedToUnion_restriction hπ data H k hj u hu b).symm)

/-- The complete pair-system comparison preserves the actual retained-edge system. -/
theorem arithmeticOneInfinityNormalizedRetainedToUnionSystem_comparison (b : Bool) :
    arithmeticOneInfinityNormalizedRetainedToUnionSystem hπ data H hj u hu b ≫
      arithmeticOneInfinityNormalizedFullComparisonSystem hπ data H hj u hu =
        arithmeticOneInfinityNormalizedTargetLeftSystem data H b := by
  ext k : 2
  exact arithmeticOneInfinityNormalizedRetainedToUnion_comparison hπ data H k hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
