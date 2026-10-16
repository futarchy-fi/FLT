/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticPositiveLabeledDescent

/-!
# The cyclic-edge universal property of the original positive-retention model

Global morphisms correspond to full labeled chart families satisfying exactly
the infinity, initial, adjacent and terminal equations. This retains the original
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
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "U" => arithmeticLabeledOpenCover hπ data H m (j + 1) hj
local notation "X" => finiteGlobalArithmeticStage hπ data (j + 1) hj m
variable {Y : Scheme.{0}}

/-- Restricting an actual morphism satisfies the original cyclic edge equations. -/
theorem arithmeticPositiveLabeled_restrictions (g : X ⟶ Y) :
    arithmeticInitialInfinityCompatible hπ data H m (j + 1) hj (fun i => c i ≫ g) ∧
      arithmeticPositiveInitialCompatible hπ data H m j hj (fun i => c i ≫ g) ∧
      arithmeticPositiveAdjacentCompatible hπ data H m j hj (fun i => c i ≫ g) ∧
      arithmeticPositiveTerminalCompatible hπ data H m j hj (fun i => c i ≫ g) := by
  apply (arithmeticPositiveLabeled_compatible_iff hπ data H m j hj (fun i => c i ≫ g)).mp
  intro i k
  simpa only [← Category.assoc] using
    congrArg (fun t => t ≫ g) (pullback.condition (f := c i) (g := c k))

/-- The original stage is characterized by the full cyclic edge equations. -/
def arithmeticPositiveLabeledHomEquiv : (X ⟶ Y) ≃
    {f : ∀ i, arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ⟶ Y //
      arithmeticInitialInfinityCompatible hπ data H m (j + 1) hj f ∧
        arithmeticPositiveInitialCompatible hπ data H m j hj f ∧
        arithmeticPositiveAdjacentCompatible hπ data H m j hj f ∧
        arithmeticPositiveTerminalCompatible hπ data H m j hj f} where
  toFun g := ⟨fun i => c i ≫ g, arithmeticPositiveLabeled_restrictions hπ data H m j hj g⟩
  invFun f := arithmeticPositiveLabeledDesc hπ data H m j hj f.val
      f.property.1 f.property.2.1 f.property.2.2.1 f.property.2.2.2
  left_inv g := by
    apply arithmeticPositiveLabeled_hom_ext hπ data H m j hj
    intro i
    exact arithmeticPositiveLabeledDesc_chart hπ data H m j hj _ _ _ _ _ i
  right_inv f := by
    apply Subtype.ext
    funext i
    exact arithmeticPositiveLabeledDesc_chart hπ data H m j hj f.val
      f.property.1 f.property.2.1 f.property.2.2.1 f.property.2.2.2 i

/-- The forward universal comparison is precisely restriction along each original chart. -/
theorem arithmeticPositiveLabeledHomEquiv_apply (g : X ⟶ Y) (i : ArithmeticChartLabel (j + 1)) :
    (arithmeticPositiveLabeledHomEquiv hπ data H m j hj g).val i = c i ≫ g := rfl

/-- The inverse universal comparison has the supplied original chart functions. -/
@[reassoc] theorem arithmeticPositiveLabeledHomEquiv_symm_chart
    (f : {f : ∀ i, arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ⟶ Y //
      arithmeticInitialInfinityCompatible hπ data H m (j + 1) hj f ∧
        arithmeticPositiveInitialCompatible hπ data H m j hj f ∧
        arithmeticPositiveAdjacentCompatible hπ data H m j hj f ∧
        arithmeticPositiveTerminalCompatible hπ data H m j hj f})
    (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ (arithmeticPositiveLabeledHomEquiv hπ data H m j hj).symm f = f.val i :=
  arithmeticPositiveLabeledDesc_chart hπ data H m j hj f.val
      f.property.1 f.property.2.1 f.property.2.2.1 f.property.2.2.2 i

end FLT.Mazur.WeierstrassDividedDepth
