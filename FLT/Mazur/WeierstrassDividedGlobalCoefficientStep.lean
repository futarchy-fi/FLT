/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientActionLaws

/-!
# Actual successor contractions after coefficient extension

Each original finite step induces its actual pullback on the whole tensor
models. The intrinsic extended action commutes with every such contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj)
local notation "next" => finiteGlobalStructure hπ data (j + 1) hj

/-- The original successor contraction on the actual coefficient-extended models. -/
def finiteGlobalCoefficientStep : finiteGlobalTensorModel hπ data S (j + 1) hj ⟶
    finiteGlobalTensorModel hπ data S j (Nat.le_of_succ_le hj) :=
  pullback.lift (pullback.fst q next)
    (pullback.snd q next ≫ finiteGlobalStep hπ data j hj) (by
      rw [Category.assoc, finiteGlobalStep_structure, pullback.condition])

/-- Coefficient-extended successor contraction retains the extended structure map. -/
@[reassoc] theorem finiteGlobalCoefficientStep_structure :
    finiteGlobalCoefficientStep hπ data j hj S ≫ pullback.fst q base = pullback.fst q next :=
  pullback.lift_fst _ _ _

/-- Projection of the extended step is precisely the original successor contraction. -/
@[reassoc] theorem finiteGlobalCoefficientStep_projection :
    finiteGlobalCoefficientStep hπ data j hj S ≫ pullback.snd q base =
      pullback.snd q next ≫ finiteGlobalStep hπ data j hj := pullback.lift_snd _ _ _

/-- Every extended successor step is equivariant for the actual extended smooth action. -/
@[reassoc] theorem finiteGlobalCoefficientPointAction_step {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S (j + 1) hj)
    (h : a ≫ integralSmoothStructure V = b ≫ pullback.fst q next) :
    finiteGlobalCoefficientPointAction hπ data (j + 1) hj S a b h ≫
        finiteGlobalCoefficientStep hπ data j hj S =
      finiteGlobalCoefficientPointAction hπ data j (Nat.le_of_succ_le hj) S a
        (b ≫ finiteGlobalCoefficientStep hπ data j hj S)
        (by rw [Category.assoc, finiteGlobalCoefficientStep_structure]; exact h) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteGlobalCoefficientStep_structure,
      finiteGlobalCoefficientPointAction_structure]
  · simp only [Category.assoc, finiteGlobalCoefficientStep_projection,
      finiteGlobalCoefficientPointAction_projection_assoc,
      finiteGlobalCoefficientPointAction_projection, finiteGlobalPointAction_step]

/-- The coefficient-extended successor square is Cartesian on the whole models. -/
theorem finiteGlobalCoefficientStep_isPullback :
    IsPullback (pullback.snd q next) (finiteGlobalCoefficientStep hπ data j hj S)
      (finiteGlobalStep hπ data j hj) (pullback.snd q base) := by
  apply IsPullback.of_bot _ (finiteGlobalCoefficientStep_projection hπ data j hj S).symm
    (IsPullback.of_hasPullback q base).flip
  simpa only [finiteGlobalCoefficientStep_structure, finiteGlobalStep_structure] using
    (IsPullback.of_hasPullback q next).flip

end FLT.Mazur.WeierstrassDividedDepth
