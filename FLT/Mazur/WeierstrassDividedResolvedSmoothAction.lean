/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalActionSmoothLocus

/-!
# The original smooth group acts on the full resolved smooth open

Restrict the actual whole-model action using its proved invariant domain.
The map retains both the coefficient morphism and the original contraction;
the second input ranges over every resolved smooth component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Restrict the actual action to an arbitrary point of the full resolved smooth open. -/
def finiteGlobalSmoothPointAction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ (U).ι ≫ base) : T ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι
    (finiteGlobalPointAction hπ data j hj a (b ≫ (U).ι) (by simpa using h)) (by
      rw [Scheme.Opens.range_ι]
      have he := finiteGlobalPointAction_preimage_smooth hπ data j hj a
        (b ≫ (U).ι) (by simpa using h)
      rw [Scheme.Hom.comp_preimage, (U).ι_preimage_self] at he
      rintro _ ⟨x, rfl⟩
      exact he.ge (Set.mem_univ x))

/-- The restricted map is exactly the original whole-model action after inclusion. -/
@[reassoc] theorem finiteGlobalSmoothPointAction_inclusion {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ (U).ι ≫ base) :
    finiteGlobalSmoothPointAction hπ data j hj a b h ≫ (U).ι =
      finiteGlobalPointAction hπ data j hj a (b ≫ (U).ι) (by simpa using h) :=
  IsOpenImmersion.lift_fac _ _ _

/-- Every resolved smooth output retains the original coefficient map. -/
@[reassoc] theorem finiteGlobalSmoothPointAction_structure {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ (U).ι ≫ base) :
    finiteGlobalSmoothPointAction hπ data j hj a b h ≫ (U).ι ≫ base =
      a ≫ integralSmoothStructure W := by
  rw [finiteGlobalSmoothPointAction_inclusion_assoc, finiteGlobalPointAction_structure]

/-- Contraction of the restricted action remains the actual original cubic addition. -/
@[reassoc] theorem finiteGlobalSmoothPointAction_contraction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen W).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ (U).ι ≫ base) :
    finiteGlobalSmoothPointAction hπ data j hj a b h ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      leftSmoothPointAddition W a ((b ≫ (U).ι) ≫ finiteGlobalContraction hπ data j hj)
        (by simpa only [finiteGlobalStructure, Category.assoc] using h) := by
  rw [finiteGlobalSmoothPointAction_inclusion_assoc, finiteGlobalPointAction_contraction]

/-- The action is natural on arbitrary test schemes, including nonflat ones. -/
theorem finiteGlobalSmoothPointAction_comp {T V : Scheme.{u}} (p : V ⟶ T)
    (a : T ⟶ (integralSmoothOpen W).toScheme) (b : T ⟶ (U).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ (U).ι ≫ base) :
    finiteGlobalSmoothPointAction hπ data j hj (p ≫ a) (p ≫ b)
        (by simpa only [Category.assoc] using congrArg (p ≫ ·) h) =
      p ≫ finiteGlobalSmoothPointAction hπ data j hj a b h := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalSmoothPointAction_inclusion, Category.assoc,
    ← finiteGlobalPointAction_comp]

/-- The universal restricted action has every resolved smooth point as its second factor. -/
def finiteGlobalSmoothAction :
    pullback (integralSmoothStructure W) ((U).ι ≫ base) ⟶ (U).toScheme :=
  finiteGlobalSmoothPointAction hπ data j hj (pullback.fst _ _) (pullback.snd _ _)
    pullback.condition

/-- The universal restricted action lies over the same original coefficient scheme. -/
@[reassoc] theorem finiteGlobalSmoothAction_structure :
    finiteGlobalSmoothAction hπ data j hj ≫ (U).ι ≫ base =
      pullback.fst (integralSmoothStructure W) ((U).ι ≫ base) ≫ integralSmoothStructure W :=
  finiteGlobalSmoothPointAction_structure hπ data j hj _ _ _

end FLT.Mazur.WeierstrassDividedDepth
