/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledOverlapRestriction

/-!
# Descent along the complete original arithmetic quotient diagram

Global quotient squares are detected by every actual labeled chart. Gluing
compatible full chart maps commutes with the original arithmetic restriction.
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
local notation "U₀" => arithmeticLabeledOpenCover hπ data H m k hk
local notation "U₁" => arithmeticLabeledOpenCover hπ data H (m + 1) k hk
local notation "r" => arithmeticLabeledAtlasRestriction hπ data H m k hk
local notation "q" => finiteGlobalArithmeticRestriction hπ data k hk m

/-- A global quotient square is equivalent to all of its original full chart squares. -/
theorem arithmeticLabeledQuotient_square_iff {Y₀ Y₁ : Scheme.{0}}
    (g₀ : finiteGlobalArithmeticStage hπ data k hk m ⟶ Y₀)
    (g₁ : finiteGlobalArithmeticStage hπ data k hk (m + 1) ⟶ Y₁) (t : Y₀ ⟶ Y₁) :
    q ≫ g₁ = g₀ ≫ t ↔ ∀ i, r i ≫ c₁ i ≫ g₁ = c₀ i ≫ g₀ ≫ t := by
  constructor
  · intro h i
    rw [← Category.assoc, arithmeticLabeledAtlasMap_restriction, Category.assoc, h]
  · intro h
    apply (U₀).hom_ext
    intro i
    change c₀ i ≫ q ≫ g₁ = c₀ i ≫ g₀ ≫ t
    rw [← Category.assoc, ← arithmeticLabeledAtlasMap_restriction, Category.assoc]
    exact h i

/-- Gluing the restricted full chart maps equals restriction of the original global gluing. -/
theorem arithmeticLabeledGlue_restriction {Y : Scheme.{0}}
    (f : ∀ i, arithmeticLabeledAtlasObject hπ data H (m + 1) k hk i ⟶ Y)
    (hf : ∀ i j, pullback.fst (c₁ i) (c₁ j) ≫ f i =
      pullback.snd (c₁ i) (c₁ j) ≫ f j) :
    q ≫ (U₁).glueMorphisms f hf =
      (U₀).glueMorphisms (fun i => r i ≫ f i)
        (arithmeticLabeledAtlasRestriction_compatible hπ data H m k hk f hf) := by
  apply (U₀).hom_ext
  intro i
  change c₀ i ≫ _ = c₀ i ≫ _
  have h₁ : c₁ i ≫ (U₁).glueMorphisms f hf = f i := (U₁).ι_glueMorphisms f hf i
  have h₀ : c₀ i ≫ (U₀).glueMorphisms (fun i => r i ≫ f i)
      (arithmeticLabeledAtlasRestriction_compatible hπ data H m k hk f hf) = r i ≫ f i :=
    (U₀).ι_glueMorphisms _ _ i
  rw [← Category.assoc, ← arithmeticLabeledAtlasMap_restriction, Category.assoc, h₁, h₀]

end FLT.Mazur.WeierstrassDividedDepth
