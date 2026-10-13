/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Arbitrary scheme maps out of a coproduct in a coefficient slice

The forgetful functor preserves the full coproduct. In particular its underlying
scheme supports descent of semilinear maps with a changing coefficient morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.OverCoproductScheme
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S : Scheme.{u}} {ι : Type} (X : ι → Over S) {Y : Scheme.{u}}

/-- Assemble arbitrary underlying scheme maps from all original slice summands. -/
def desc (f : (i : ι) → (X i).left ⟶ Y) : (∐ X).left ⟶ Y :=
  inv (sigmaComparison (Over.forget S) X) ≫ Sigma.desc f

/-- Each full original summand receives its specified scheme map. -/
@[reassoc] theorem ι_desc (f : (i : ι) → (X i).left ⟶ Y) (i : ι) :
    (Sigma.ι X i).left ≫ desc X f = f i := by
  change (Over.forget S).map (Sigma.ι X i) ≫
    inv (sigmaComparison (Over.forget S) X) ≫ Sigma.desc f = _
  rw [map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_comp_desc]

/-- Equality into arbitrary schemes is detected by the full original slice summands. -/
theorem hom_ext (f g : (∐ X).left ⟶ Y)
    (h : ∀ i, (Sigma.ι X i).left ≫ f = (Sigma.ι X i).left ≫ g) : f = g := by
  apply (cancel_epi (sigmaComparison (Over.forget S) X)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [ι_comp_sigmaComparison_assoc, Over.forget_map] using h i

end FLT.Mazur.OverCoproductScheme
