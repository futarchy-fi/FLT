/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalOriginalSmoothPoints
public import FLT.Mazur.WeierstrassDividedSmoothCoefficientEmbedding

/-!
# The actual finite action after arbitrary coefficient extension

The original coefficient-extended smooth scheme acts by a constructed map
on the full tensor model. Its projection is the original integral action.
No flatness or splitting hypothesis is imposed on the coefficient algebra.
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

variable (j : ℕ) (hj : j ≤ n)

variable (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst q base
local notation "snd" => pullback.snd q base

/-- Coefficient-compatible inputs form a pair for the original integral action. -/
theorem finiteGlobalCoefficientInput_condition {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    (a ≫ originalSmoothCoefficientMap S W) ≫ integralSmoothStructure W =
      (b ≫ snd) ≫ base := by
  calc
    _ = (a ≫ integralSmoothStructure V) ≫ q := by
      simp only [Category.assoc, originalSmoothCoefficientMap_structure]
    _ = (b ≫ fst) ≫ q := congrArg (fun f => f ≫ q) h
    _ = (b ≫ snd) ≫ base := by simp only [Category.assoc, pullback.condition]

/-- The original extended smooth parameter acts on every point of the full tensor model. -/
def finiteGlobalCoefficientPointAction {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    T ⟶ finiteGlobalTensorModel hπ data S j hj :=
  pullback.lift (a ≫ integralSmoothStructure V)
    (finiteGlobalPointAction hπ data j hj (a ≫ originalSmoothCoefficientMap S W) (b ≫ snd)
      (finiteGlobalCoefficientInput_condition hπ data j hj S a b h))
    (by simp only [finiteGlobalPointAction_structure, Category.assoc,
          originalSmoothCoefficientMap_structure])

/-- The extended action preserves its actual coefficient morphism. -/
@[reassoc] theorem finiteGlobalCoefficientPointAction_structure {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    finiteGlobalCoefficientPointAction hπ data j hj S a b h ≫ fst =
      a ≫ integralSmoothStructure V := pullback.lift_fst _ _ _

/-- Forgetting the coefficient extension recovers exactly the original integral action. -/
@[reassoc] theorem finiteGlobalCoefficientPointAction_projection {T : Scheme.{u}}
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    finiteGlobalCoefficientPointAction hπ data j hj S a b h ≫ snd =
      finiteGlobalPointAction hπ data j hj (a ≫ originalSmoothCoefficientMap S W) (b ≫ snd)
        (finiteGlobalCoefficientInput_condition hπ data j hj S a b h) := pullback.lift_snd _ _ _

/-- The constructed coefficient action is natural on arbitrary schemes of points. -/
theorem finiteGlobalCoefficientPointAction_comp {T U : Scheme.{u}} (p : U ⟶ T)
    (a : T ⟶ (integralSmoothOpen V).toScheme)
    (b : T ⟶ finiteGlobalTensorModel hπ data S j hj)
    (h : a ≫ integralSmoothStructure V = b ≫ fst) :
    finiteGlobalCoefficientPointAction hπ data j hj S (p ≫ a) (p ≫ b)
        (by simp only [Category.assoc, h]) =
      p ≫ finiteGlobalCoefficientPointAction hπ data j hj S a b h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finiteGlobalCoefficientPointAction_structure]
  · simp only [Category.assoc, finiteGlobalCoefficientPointAction_projection]
    exact finiteGlobalPointAction_comp hπ data j hj p
      (a ≫ originalSmoothCoefficientMap S W) (b ≫ snd) _

/-- The actual whole action morphism after an arbitrary extension of coefficients. -/
def finiteGlobalCoefficientAction :
    pullback (integralSmoothStructure V) fst ⟶ finiteGlobalTensorModel hπ data S j hj :=
  finiteGlobalCoefficientPointAction hπ data j hj S
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition

/-- The extended action is an actual morphism over the extended coefficient spectrum. -/
@[reassoc] theorem finiteGlobalCoefficientAction_structure :
    finiteGlobalCoefficientAction hπ data j hj S ≫ fst =
      pullback.fst _ _ ≫ integralSmoothStructure V :=
  finiteGlobalCoefficientPointAction_structure hπ data j hj S _ _ _

end FLT.Mazur.WeierstrassDividedDepth
