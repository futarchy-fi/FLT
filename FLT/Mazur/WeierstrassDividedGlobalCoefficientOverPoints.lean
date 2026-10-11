/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientSmoothOrbit
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# Intrinsic group actions on coefficient-extended model points

The actual extended smooth group acts on the whole tensor model.
Its action on every test scheme retains the independently constructed operations.
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

variable (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "base" => pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap R S))) (finiteGlobalStructure hπ data j hj)
variable (T : Over (Spec (.of S)))

/-- The intrinsic point group acts by the actual whole finite-model morphism. -/
def finiteGlobalCoefficientOverPointAction
    (a : T ⟶ (integralSmoothGroup V).X)
    (b : T ⟶ Over.mk base) :
    T ⟶ Over.mk base :=
  Over.homMk (finiteGlobalCoefficientPointAction hπ data j hj S a.left b.left
    (a.w.trans b.w.symm))
    ((finiteGlobalCoefficientPointAction_structure hπ data j hj S a.left b.left _).trans a.w)

/-- The action on points over the base has the intrinsic identity. -/
theorem finiteGlobalCoefficientOverPointAction_one
    (b : T ⟶ Over.mk base) :
    finiteGlobalCoefficientOverPointAction hπ data j hj S T 1 b = b := by
  apply Over.OverMorphism.ext
  change finiteGlobalCoefficientPointAction hπ data j hj S
    (T.hom ≫ integralSmoothZero V) b.left
      (by rw [Category.assoc, integralSmoothZero_structure, Category.comp_id];
          exact b.w.symm) = b.left
  have he := finiteGlobalCoefficientPointAction_zero hπ data j hj S b.left
  have hb : b.left ≫ base = T.hom := b.w
  simpa only [← Category.assoc, hb] using he

/-- Intrinsic group multiplication acts associatively on all finite-model points. -/
theorem finiteGlobalCoefficientOverPointAction_mul
    (a b : T ⟶ (integralSmoothGroup V).X)
    (c : T ⟶ Over.mk base) :
    finiteGlobalCoefficientOverPointAction hπ data j hj S T (a * b) c =
      finiteGlobalCoefficientOverPointAction hπ data j hj S T a
        (finiteGlobalCoefficientOverPointAction hπ data j hj S T b c) := by
  apply Over.OverMorphism.ext
  exact finiteGlobalCoefficientPointAction_assoc hπ data j hj S a.left b.left c.left
    (a.w.trans b.w.symm) (b.w.trans c.w.symm)

/-- Every scheme over the coefficient base has the proved intrinsic smooth group action. -/
instance finiteGlobalCoefficientPointMulAction :
    MulAction (T ⟶ (integralSmoothGroup V).X)
      (T ⟶ Over.mk base) where
  smul := finiteGlobalCoefficientOverPointAction hπ data j hj S T
  one_smul := finiteGlobalCoefficientOverPointAction_one hπ data j hj S T
  mul_smul := finiteGlobalCoefficientOverPointAction_mul hπ data j hj S T

/-- Restriction of points commutes with the actual group action over the base. -/
theorem finiteGlobalCoefficientOverPointAction_comp {U : Over (Spec (.of S))} (p : U ⟶ T)
    (a : T ⟶ (integralSmoothGroup V).X)
    (b : T ⟶ Over.mk base) :
    finiteGlobalCoefficientOverPointAction hπ data j hj S U (p ≫ a) (p ≫ b) =
      p ≫ finiteGlobalCoefficientOverPointAction hπ data j hj S T a b := by
  apply Over.OverMorphism.ext
  exact finiteGlobalCoefficientPointAction_comp hπ data j hj S p.left a.left b.left
    (a.w.trans b.w.symm)

end FLT.Mazur.WeierstrassDividedDepth
