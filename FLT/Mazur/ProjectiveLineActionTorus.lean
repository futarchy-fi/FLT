/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothLocus
public import FLT.Mazur.ProjectiveLineActionAssociativity

/-!
# Restriction of universal scaling to the multiplicative torus

Affine algebra points identify the actual torus restriction with Hopf
multiplication. The tensor spectrum comparison proves equality of morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped Polynomial LaurentPolynomial TensorProduct
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ProjectiveLineActionTorus
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open ProjectiveLineProductCharts ProjectiveLineUniversalAction ProjectiveLineActionPoints
open ProjectiveLineActionAssociativity PolygonPinching
variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
@[reassoc] theorem groupPoint_torus (a : Aˣ) :
    groupPoint K A a ≫ (torusToComponent K).left = chartPoint K A (a : A) false := by
  change Spec.map _ ≫ (Spec.map _ ≫ ProjectiveLine.left K) =
    Spec.map _ ≫ ProjectiveLine.left K
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  ext <;> simp [LaurentUnitPoints.evalUnit]

theorem torus_at (a c : Aˣ)
    (f : Spec (.of A) ⟶
      (MultiplicativeGroupScheme.gm K ⊗ MultiplicativeGroupScheme.gm K).left)
    (hf : f ≫ pullback.fst _ _ = groupPoint K A a)
    (hs : f ≫ pullback.snd _ _ = groupPoint K A c) :
    f ≫ (MultiplicativeGroupScheme.gm K ◁ torusToComponent K).left ≫ action K =
      f ≫ μ[MultiplicativeGroupScheme.gm K].left ≫ (torusToComponent K).left := by
  have hl := chart_action K A a (c : A) false
    (f ≫ (MultiplicativeGroupScheme.gm K ◁ torusToComponent K).left)
    (by simp only [Category.assoc]
        erw [Over.whiskerLeft_left_fst
          (R := MultiplicativeGroupScheme.gm K) (torusToComponent K)]
        exact hf)
    (by simp only [Category.assoc]
        erw [Over.whiskerLeft_left_snd
          (R := MultiplicativeGroupScheme.gm K) (torusToComponent K)]
        rw [← Category.assoc, hs, groupPoint_torus])
  have hr := congrArg (· ≫ (torusToComponent K).left) (groupPoint_mul K A a c f hf hs)
  rw [groupPoint_torus] at hr
  simpa only [Category.assoc, Bool.false_eq_true, ↓reduceIte, Units.val_mul] using
    hl.trans hr.symm

@[reassoc] theorem torus_act : MultiplicativeGroupScheme.gm K ◁ torusToComponent K ≫ act K =
    μ[MultiplicativeGroupScheme.gm K] ≫ torusToComponent K := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullbackSpecIso K (parameter K) (parameter K)).inv).mp
  apply torus_at K (pairRing K)
    (LaurentUnitPoints.pointUnit Algebra.TensorProduct.includeLeft)
    (LaurentUnitPoints.pointUnit Algebra.TensorProduct.includeRight)
  · rw [groupPoint_pointUnit]
    exact pullbackSpecIso_inv_fst K (parameter K) (parameter K)
  · rw [groupPoint_pointUnit]
    exact pullbackSpecIso_inv_snd K (parameter K) (parameter K)
end FLT.Mazur.ProjectiveLineActionTorus
