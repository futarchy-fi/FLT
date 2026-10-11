/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientOverPoints

/-!
# The actual coefficient action as a relative morphism

Package the previously constructed action on arbitrary points as its universal
relative morphism, with evaluation and projection formulas that avoid unfolding products.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory
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
local notation "H" => integralSmoothGroup V
local notation "C" => Over.mk base

/-- The intrinsic coefficient smooth group acts by this actual relative morphism. -/
def finiteGlobalCoefficientOverAction : (H).X ⊗ C ⟶ C :=
  finiteGlobalCoefficientOverPointAction hπ data j hj S ((H).X ⊗ C) (fst (H).X C) (snd (H).X C)

/-- The relative morphism evaluates to the already constructed action on every test scheme. -/
theorem finiteGlobalCoefficientOverAction_points {T : Over (Spec (.of S))}
    (a : T ⟶ (H).X) (b : T ⟶ C) :
    lift a b ≫ finiteGlobalCoefficientOverAction hπ data j hj S = a • b := by
  change lift a b ≫ finiteGlobalCoefficientOverAction hπ data j hj S =
    finiteGlobalCoefficientOverPointAction hπ data j hj S T a b
  have h := finiteGlobalCoefficientOverPointAction_comp hπ data j hj S ((H).X ⊗ C)
    (lift a b) (fst (H).X C) (snd (H).X C)
  simpa only [lift_fst, lift_snd, finiteGlobalCoefficientOverAction] using h.symm

/-- A pointwise comparison proves equality with the actual relative action morphism. -/
theorem finiteGlobalCoefficientOverAction_ext (f : (H).X ⊗ C ⟶ C)
    (h : ∀ (T : Over (Spec (.of S))) (a : T ⟶ (H).X) (b : T ⟶ C),
      lift a b ≫ f = a • b) : f = finiteGlobalCoefficientOverAction hπ data j hj S := by
  have he := h ((H).X ⊗ C) (fst (H).X C) (snd (H).X C)
  rw [lift_fst_snd, Category.id_comp] at he
  exact he

end FLT.Mazur.WeierstrassDividedDepth
