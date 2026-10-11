/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalPointSubgroups

/-!
# Equivariance of every actual finite step

Original smooth translations commute with the actual contractions between
successive whole models. Their retained smooth point orbits also agree.
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

variable (j : ℕ) (hj : j + 1 ≤ n)

variable (T : Over (Spec (.of R)))


/-- The actual successor contraction viewed over its original coefficient spectrum. -/
def finiteGlobalStepOver :
    Over.mk (finiteGlobalStructure hπ data (j + 1) hj) ⟶
      Over.mk (finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj)) :=
  Over.homMk (finiteGlobalStep hπ data j hj) (finiteGlobalStep_structure hπ data j hj)

/-- The whole action commutes with every actual successor contraction over the base. -/
theorem finiteGlobalOverPointAction_step
    (a : T ⟶ (integralSmoothGroup W).X)
    (b : T ⟶ Over.mk (finiteGlobalStructure hπ data (j + 1) hj)) :
    finiteGlobalOverPointAction hπ data (j + 1) hj T a b ≫ finiteGlobalStepOver hπ data j hj =
      finiteGlobalOverPointAction hπ data j (Nat.le_of_succ_le hj) T a
        (b ≫ finiteGlobalStepOver hπ data j hj) := by
  apply Over.OverMorphism.ext
  exact finiteGlobalPointAction_step hπ data j hj a.left b.left _

/-- Each original point keeps its retained smooth image under every successor contraction. -/
@[reassoc] theorem finiteGlobalSmoothOverPoint_step
    (a : T ⟶ (integralSmoothGroup W).X) :
    finiteGlobalSmoothOverPoint hπ data (j + 1) hj T a ≫ finiteGlobalStepOver hπ data j hj =
      finiteGlobalSmoothOverPoint hπ data j (Nat.le_of_succ_le hj) T a := by
  apply Over.OverMorphism.ext
  change (a.left ≫ finiteGlobalSmoothEmbedding hπ data (j + 1) hj) ≫
    finiteGlobalStep hπ data j hj = _
  rw [Category.assoc, finiteGlobalSmoothEmbedding_step]
  rfl

/-- The faithful translation permutations commute with the original finite steps. -/
theorem finiteGlobalPointPermutation_step
    (a : T ⟶ (integralSmoothGroup W).X)
    (b : T ⟶ Over.mk (finiteGlobalStructure hπ data (j + 1) hj)) :
    finiteGlobalPointPermutation hπ data (j + 1) hj T a b ≫ finiteGlobalStepOver hπ data j hj =
      finiteGlobalPointPermutation hπ data j (Nat.le_of_succ_le hj) T a
        (b ≫ finiteGlobalStepOver hπ data j hj) :=
  finiteGlobalOverPointAction_step hπ data j hj T a b

end FLT.Mazur.WeierstrassDividedDepth
