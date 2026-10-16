/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlasRestriction

/-!
# Quotient restriction on all original labeled intersections

The complete atlas square induces the actual map of every pairwise fiber
product, retaining both original projections. Compatible chart maps restrict
to compatible maps without any new intersection assumptions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "c₀" => arithmeticLabeledAtlasMap hπ data H m k hk
local notation "c₁" => arithmeticLabeledAtlasMap hπ data H (m + 1) k hk
local notation "r" => arithmeticLabeledAtlasRestriction hπ data H m k hk

/-- Restriction on every actual labeled intersection, retaining its two original projections. -/
def arithmeticLabeledOverlapRestriction (i j : ArithmeticChartLabel k) :
    pullback (c₀ i) (c₀ j) ⟶ pullback (c₁ i) (c₁ j) :=
  pullback.lift (pullback.fst _ _ ≫ r i) (pullback.snd _ _ ≫ r j) (by
    simp only [Category.assoc, arithmeticLabeledAtlasMap_restriction]
    rw [← Category.assoc, pullback.condition, Category.assoc])

/-- The original first overlap projection commutes with the quotient map. -/
@[reassoc] theorem arithmeticLabeledOverlapRestriction_fst (i j : ArithmeticChartLabel k) :
    arithmeticLabeledOverlapRestriction hπ data H m k hk i j ≫ pullback.fst _ _ =
      pullback.fst (c₀ i) (c₀ j) ≫ r i :=
  pullback.lift_fst _ _ _

/-- The original second overlap projection commutes with the quotient map. -/
@[reassoc] theorem arithmeticLabeledOverlapRestriction_snd (i j : ArithmeticChartLabel k) :
    arithmeticLabeledOverlapRestriction hπ data H m k hk i j ≫ pullback.snd _ _ =
      pullback.snd (c₀ i) (c₀ j) ≫ r j :=
  pullback.lift_snd _ _ _

/-- Compatible maps on all upper-order charts remain compatible after actual restriction. -/
theorem arithmeticLabeledAtlasRestriction_compatible {Y : Scheme.{0}}
    (f : ∀ i, arithmeticLabeledAtlasObject hπ data H (m + 1) k hk i ⟶ Y)
    (hf : ∀ i j, pullback.fst (c₁ i) (c₁ j) ≫ f i =
      pullback.snd (c₁ i) (c₁ j) ≫ f j) (i j : ArithmeticChartLabel k) :
    pullback.fst (c₀ i) (c₀ j) ≫ r i ≫ f i =
      pullback.snd (c₀ i) (c₀ j) ≫ r j ≫ f j := by
  have h := congrArg
    (fun g => arithmeticLabeledOverlapRestriction hπ data H m k hk i j ≫ g) (hf i j)
  simpa only [← Category.assoc, arithmeticLabeledOverlapRestriction_fst,
    arithmeticLabeledOverlapRestriction_snd] using h

end FLT.Mazur.WeierstrassDividedDepth
