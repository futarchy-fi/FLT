/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalOriginalSmoothPoints
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# Group actions on points over the coefficient spectrum

The constructed action makes all finite-model points a set acted on by the
original smooth point group. The scheme maps and coefficient maps are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

variable (j : ℕ) (hj : j ≤ n)

variable (T : Over (Spec (.of R)))

/-- The original point group acts by the actual whole finite-model morphism. -/
def finiteGlobalOverPointAction
    (a : T ⟶ (integralSmoothGroup W).X)
    (b : T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) :
    T ⟶ Over.mk (finiteGlobalStructure hπ data j hj) :=
  Over.homMk (finiteGlobalPointAction hπ data j hj a.left b.left
    (a.w.trans b.w.symm))
    ((finiteGlobalPointAction_structure hπ data j hj a.left b.left _).trans a.w)

/-- The action on points over the base has the original identity. -/
theorem finiteGlobalOverPointAction_one
    (b : T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) :
    finiteGlobalOverPointAction hπ data j hj T 1 b = b := by
  apply Over.OverMorphism.ext
  change finiteGlobalPointAction hπ data j hj
    (T.hom ≫ integralSmoothZero W) b.left _ = b.left
  have he := finiteGlobalPointAction_zero hπ data j hj b.left
  have hb : b.left ≫ finiteGlobalStructure hπ data j hj = T.hom := b.w
  simpa only [← Category.assoc, hb] using he

/-- Original group multiplication acts associatively on all finite-model points. -/
theorem finiteGlobalOverPointAction_mul
    (a b : T ⟶ (integralSmoothGroup W).X)
    (c : T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) :
    finiteGlobalOverPointAction hπ data j hj T (a * b) c =
      finiteGlobalOverPointAction hπ data j hj T a
        (finiteGlobalOverPointAction hπ data j hj T b c) := by
  apply Over.OverMorphism.ext
  exact finiteGlobalPointAction_assoc hπ data j hj a.left b.left c.left
    (a.w.trans b.w.symm) (b.w.trans c.w.symm)

/-- Every scheme over the coefficient base has the proved original smooth group action. -/
instance finiteGlobalPointMulAction :
    MulAction (T ⟶ (integralSmoothGroup W).X)
      (T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) where
  smul := finiteGlobalOverPointAction hπ data j hj T
  one_smul := finiteGlobalOverPointAction_one hπ data j hj T
  mul_smul := finiteGlobalOverPointAction_mul hπ data j hj T

/-- Restriction of points commutes with the actual group action over the base. -/
theorem finiteGlobalOverPointAction_comp {U : Over (Spec (.of R))} (p : U ⟶ T)
    (a : T ⟶ (integralSmoothGroup W).X)
    (b : T ⟶ Over.mk (finiteGlobalStructure hπ data j hj)) :
    finiteGlobalOverPointAction hπ data j hj U (p ≫ a) (p ≫ b) =
      p ≫ finiteGlobalOverPointAction hπ data j hj T a b := by
  apply Over.OverMorphism.ext
  exact finiteGlobalPointAction_comp hπ data j hj p.left a.left b.left _

end FLT.Mazur.WeierstrassDividedDepth
