/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroLabeledDescent

/-!
# The four-equation universal property of the original stage-zero model

Global morphisms correspond to full labeled chart families satisfying exactly
the two infinity and two standard terminal equations. This retains the original
cover and avoids any assumed gluing comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m 0 (Nat.zero_le n)
local notation "U" => arithmeticLabeledOpenCover hπ data H m 0 (Nat.zero_le n)
local notation "X" => finiteGlobalArithmeticStage hπ data 0 (Nat.zero_le n) m
variable {Y : Scheme.{0}}

/-- Restricting an actual stage-zero morphism satisfies the four original endpoint equations. -/
theorem arithmeticZeroLabeled_restrictions (g : X ⟶ Y) :
    arithmeticInitialInfinityCompatible hπ data H m 0 (Nat.zero_le n) (fun i => c i ≫ g) ∧
      arithmeticZeroTerminalCompatible hπ data m H (fun i => c i ≫ g) := by
  apply (arithmeticZeroLabeled_compatible_iff hπ data H m (fun i => c i ≫ g)).mp
  intro i j
  simpa only [← Category.assoc] using
    congrArg (fun t => t ≫ g) (pullback.condition (f := c i) (g := c j))

/-- The original stage is characterized by the four full standard endpoint equations. -/
def arithmeticZeroLabeledHomEquiv : (X ⟶ Y) ≃
    {f : ∀ i, arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) i ⟶ Y //
      arithmeticInitialInfinityCompatible hπ data H m 0 (Nat.zero_le n) f ∧
        arithmeticZeroTerminalCompatible hπ data m H f} where
  toFun g := ⟨fun i => c i ≫ g, arithmeticZeroLabeled_restrictions hπ data H m g⟩
  invFun f := arithmeticZeroLabeledDesc hπ data H m f.val f.property.1 f.property.2
  left_inv g := by
    apply arithmeticZeroLabeled_hom_ext hπ data H m
    intro i
    exact arithmeticZeroLabeledDesc_chart hπ data H m _ _ _ i
  right_inv f := by
    apply Subtype.ext
    funext i
    exact arithmeticZeroLabeledDesc_chart hπ data H m f.val f.property.1 f.property.2 i

/-- The forward universal comparison is precisely restriction along each original chart. -/
theorem arithmeticZeroLabeledHomEquiv_apply (g : X ⟶ Y) (i : ArithmeticChartLabel 0) :
    (arithmeticZeroLabeledHomEquiv hπ data H m g).val i = c i ≫ g := rfl

/-- The inverse universal comparison has the supplied original chart functions. -/
@[reassoc] theorem arithmeticZeroLabeledHomEquiv_symm_chart
    (f : {f : ∀ i, arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) i ⟶ Y //
      arithmeticInitialInfinityCompatible hπ data H m 0 (Nat.zero_le n) f ∧
        arithmeticZeroTerminalCompatible hπ data m H f}) (i : ArithmeticChartLabel 0) :
    c i ≫ (arithmeticZeroLabeledHomEquiv hπ data H m).symm f = f.val i :=
  arithmeticZeroLabeledDesc_chart hπ data H m f.val f.property.1 f.property.2 i

end FLT.Mazur.WeierstrassDividedDepth
